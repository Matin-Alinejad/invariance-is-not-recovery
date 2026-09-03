#!/usr/bin/env python3
"""Compute paired retention-sensitivity and matched target-local/global contrasts.

Statistical unit
----------------
Graph/seed is the independent Monte Carlo replication unit. Correlated target
rows are paired within target and averaged within graph before uncertainty is
computed across seeds. Missingness-rate comparisons use the same graph, SEM,
raw sample, and random mask stream. Dedicated-local recovery is compared only
with the same target restriction of the global estimate, never with whole-
skeleton F1.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np
import pandas as pd
from scipy.stats import t as student_t

TARGET_METRICS = [
    "precision",
    "recall",
    "f1",
    "exact_recovery",
    "fp",
    "fn",
    "trace_ci_tests",
    "trace_ci_n_eff_min",
    "trace_ci_n_eff_median",
    "trace_ci_effective_fraction_mean",
    "runtime_seconds",
]
RETENTION_METRICS = TARGET_METRICS + [
    "missing_rate_realized_masked_cells",
    "complete_row_rate",
    "selected_edge_partial_corr_min",
    "selected_edge_query_retention_min",
]


def _t_summary(values) -> dict[str, float | int]:
    array = pd.Series(values).dropna().to_numpy(float)
    n = len(array)
    if n == 0:
        return {"n": 0, "mean": np.nan, "lo95": np.nan, "hi95": np.nan, "halfwidth95": np.nan}
    mean = float(array.mean())
    if n < 2:
        return {"n": n, "mean": mean, "lo95": np.nan, "hi95": np.nan, "halfwidth95": np.nan}
    standard_error = float(array.std(ddof=1) / np.sqrt(n))
    critical = float(student_t.ppf(0.975, n - 1))
    halfwidth = critical * standard_error
    return {
        "n": n,
        "mean": mean,
        "lo95": mean - halfwidth,
        "hi95": mean + halfwidth,
        "halfwidth95": halfwidth,
    }


def analyze_local(frame: pd.DataFrame) -> pd.DataFrame:
    """Compare dedicated-local search with the matched target restriction of global PC."""
    required_scopes = {"target_restriction_of_global", "dedicated_local"}
    if not required_scopes <= set(frame["evaluation_scope"].astype(str)):
        return pd.DataFrame()

    selected = frame[frame["evaluation_scope"].isin(required_scopes)].copy()
    pair_keys = [
        "cell_id",
        "topology",
        "p",
        "gamma",
        "missingness_mode",
        "missing_rate_target",
        "alpha_schedule",
        "seed",
        "target",
    ]
    metrics = [metric for metric in TARGET_METRICS if metric in selected.columns]

    global_rows = selected[
        selected["evaluation_scope"] == "target_restriction_of_global"
    ][pair_keys + metrics].rename(
        columns={metric: f"{metric}_global_restriction" for metric in metrics}
    )
    local_rows = selected[selected["evaluation_scope"] == "dedicated_local"][
        pair_keys + metrics
    ].rename(columns={metric: f"{metric}_dedicated_local" for metric in metrics})

    paired = global_rows.merge(
        local_rows,
        on=pair_keys,
        how="inner",
        validate="one_to_one",
    ).copy()
    for metric in metrics:
        paired.loc[:, f"{metric}_delta_local_minus_global"] = (
            paired[f"{metric}_dedicated_local"].astype(float)
            - paired[f"{metric}_global_restriction"].astype(float)
        )

    if {
        "trace_ci_tests_dedicated_local",
        "trace_ci_tests_global_restriction",
    } <= set(paired.columns):
        paired.loc[:, "ci_saving_fraction"] = 1.0 - (
            paired["trace_ci_tests_dedicated_local"]
            / paired["trace_ci_tests_global_restriction"]
        )
    if {
        "runtime_seconds_dedicated_local",
        "runtime_seconds_global_restriction",
    } <= set(paired.columns):
        paired.loc[:, "runtime_saving_fraction"] = 1.0 - (
            paired["runtime_seconds_dedicated_local"]
            / paired["runtime_seconds_global_restriction"]
        )

    graph_keys = [
        "topology",
        "p",
        "gamma",
        "missingness_mode",
        "missing_rate_target",
        "alpha_schedule",
        "seed",
    ]
    numeric = [
        column
        for column in paired.columns
        if column not in pair_keys and pd.api.types.is_numeric_dtype(paired[column])
    ]

    # Single-target view: average the prespecified targets within each generated
    # graph. This answers how much one requested target neighborhood costs
    # relative to fitting the global skeleton once.
    graph_level = paired.groupby(graph_keys, dropna=False, as_index=False)[numeric].mean(
        numeric_only=True
    )

    # Batch-target view: global search is paid once, whereas dedicated-local
    # search is paid once per target. Reporting both views avoids overstating
    # local computational savings when several targets are requested together.
    batch_rows = []
    for key, group in paired.groupby(graph_keys, dropna=False):
        key = key if isinstance(key, tuple) else (key,)
        row = dict(zip(graph_keys, key))
        row["targets_in_batch"] = int(group["target"].nunique())

        if {
            "trace_ci_tests_dedicated_local",
            "trace_ci_tests_global_restriction",
        } <= set(group.columns):
            local_total = float(group["trace_ci_tests_dedicated_local"].sum())
            global_once = float(group["trace_ci_tests_global_restriction"].iloc[0])
            row["trace_ci_tests_dedicated_local_batch_total"] = local_total
            row["trace_ci_tests_global_once"] = global_once
            row["ci_saving_fraction_batch_targets"] = (
                1.0 - local_total / global_once if global_once > 0 else np.nan
            )

        if {
            "runtime_seconds_dedicated_local",
            "runtime_seconds_global_restriction",
        } <= set(group.columns):
            local_total = float(group["runtime_seconds_dedicated_local"].sum())
            global_once = float(group["runtime_seconds_global_restriction"].iloc[0])
            row["runtime_seconds_dedicated_local_batch_total"] = local_total
            row["runtime_seconds_global_once"] = global_once
            row["runtime_saving_fraction_batch_targets"] = (
                1.0 - local_total / global_once if global_once > 0 else np.nan
            )
        batch_rows.append(row)

    batch = pd.DataFrame(batch_rows)
    if len(batch):
        graph_level = graph_level.merge(
            batch,
            on=graph_keys,
            how="left",
            validate="one_to_one",
        )

    group_keys = [
        "topology",
        "p",
        "gamma",
        "missingness_mode",
        "missing_rate_target",
        "alpha_schedule",
    ]
    numeric_graph = [
        column
        for column in graph_level.columns
        if column not in graph_keys and pd.api.types.is_numeric_dtype(graph_level[column])
    ]

    rows = []
    for key, group in graph_level.groupby(group_keys, dropna=False):
        row = dict(zip(group_keys, key))
        row["n_graph_seeds"] = int(group["seed"].nunique())
        for column in numeric_graph:
            summary = _t_summary(group[column])
            for suffix, value in summary.items():
                row[f"{column}_{suffix}"] = value
        rows.append(row)
    return pd.DataFrame(rows).sort_values(group_keys).reset_index(drop=True)


def analyze_retention(frame: pd.DataFrame) -> tuple[pd.DataFrame, pd.DataFrame]:
    """Summarize retention levels and form the prespecified paired rate contrasts."""
    if frame["missing_rate_target"].nunique() < 2:
        return pd.DataFrame(), pd.DataFrame()

    metrics = [metric for metric in RETENTION_METRICS if metric in frame.columns]
    graph_keys = [
        "cell_id",
        "evaluation_scope",
        "topology",
        "p",
        "gamma",
        "missingness_mode",
        "missing_rate_target",
        "alpha_schedule",
        "seed",
    ]
    graph_level = frame.groupby(graph_keys, dropna=False, as_index=False)[metrics].mean(
        numeric_only=True
    )

    summary_keys = [
        "evaluation_scope",
        "topology",
        "p",
        "gamma",
        "missingness_mode",
        "missing_rate_target",
        "alpha_schedule",
    ]
    descriptive_rows = []
    for key, group in graph_level.groupby(summary_keys, dropna=False):
        row = dict(zip(summary_keys, key))
        row["n_graph_seeds"] = int(group["seed"].nunique())
        for metric in metrics:
            for suffix, value in _t_summary(group[metric]).items():
                row[f"{metric}_{suffix}"] = value
        descriptive_rows.append(row)
    descriptive = (
        pd.DataFrame(descriptive_rows).sort_values(summary_keys).reset_index(drop=True)
    )

    available_rates = sorted(float(value) for value in graph_level["missing_rate_target"].dropna().unique())
    contrast_rows = []
    for low_rate, high_rate in [(0.1, 0.3), (0.3, 0.5), (0.1, 0.5)]:
        if low_rate not in available_rates or high_rate not in available_rates:
            continue

        pair_keys = [
            "evaluation_scope",
            "topology",
            "p",
            "gamma",
            "missingness_mode",
            "alpha_schedule",
            "seed",
        ]
        low = graph_level[np.isclose(graph_level["missing_rate_target"], low_rate)][
            pair_keys + metrics
        ].rename(columns={metric: f"{metric}_lo" for metric in metrics})
        high = graph_level[np.isclose(graph_level["missing_rate_target"], high_rate)][
            pair_keys + metrics
        ].rename(columns={metric: f"{metric}_hi" for metric in metrics})
        paired = low.merge(high, on=pair_keys, how="inner", validate="one_to_one")

        group_keys = [column for column in pair_keys if column != "seed"]
        for key, group in paired.groupby(group_keys, dropna=False):
            row = dict(zip(group_keys, key))
            row.update(
                {
                    "rate_low": low_rate,
                    "rate_high": high_rate,
                    "contrast": f"{high_rate:.1f}_minus_{low_rate:.1f}",
                    "n_graph_seeds": int(group["seed"].nunique()),
                }
            )
            for metric in metrics:
                delta = group[f"{metric}_hi"].astype(float) - group[f"{metric}_lo"].astype(float)
                for suffix, value in _t_summary(delta).items():
                    row[f"{metric}_delta_{suffix}"] = value
            contrast_rows.append(row)

    contrasts = pd.DataFrame(contrast_rows)
    if len(contrasts):
        contrasts = contrasts.sort_values(
            ["evaluation_scope", "topology", "p", "rate_low", "rate_high"]
        ).reset_index(drop=True)
    return descriptive, contrasts


def main() -> int:
    """Compute retention-sensitivity and matched target-local/global paired analyses."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("results", help="Path to an experiment results.csv file.")
    parser.add_argument("--out-dir", required=True, help="Directory for analysis CSVs.")
    parser.add_argument(
        "--kind",
        choices=["local", "retention", "auto"],
        default="auto",
        help="Analysis branch to run (default: infer from the input).",
    )
    args = parser.parse_args()

    raw = pd.read_csv(args.results)
    if "cell_status" in raw.columns:
        raw = raw[raw["cell_status"] == "complete"].copy()

    output_dir = Path(args.out_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    if args.kind in {"local", "auto"} and "dedicated_local" in set(
        raw["evaluation_scope"].astype(str)
    ):
        local = analyze_local(raw)
        local.to_csv(output_dir / "matched_local_global_paired.csv", index=False)
        print("matched local rows:", len(local))

    if args.kind in {"retention", "auto"} and raw["missing_rate_target"].nunique() > 1:
        descriptive, contrasts = analyze_retention(raw)
        descriptive.to_csv(output_dir / "retention_summary.csv", index=False)
        contrasts.to_csv(output_dir / "retention_paired_contrasts.csv", index=False)
        print(
            "retention summary rows:",
            len(descriptive),
            "contrast rows:",
            len(contrasts),
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
