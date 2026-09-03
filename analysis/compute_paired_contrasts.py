#!/usr/bin/env python3
"""Compute dependence-aware paired contrasts for the registered experiment design.

The simulator pairs graph structure, SEM coefficients, row prefixes, and mask
uniforms across compared conditions. Target-restriction rows are therefore
averaged within each generated graph before contrasts are formed, and Student-t
uncertainty is computed across graph seeds rather than across correlated targets.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np
import pandas as pd
from scipy.stats import t as student_t

METRICS = [
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
BASE_KEYS = ["evaluation_scope", "topology", "p", "seed"]


def graph_level(frame: pd.DataFrame) -> pd.DataFrame:
    """Collapse correlated target rows to one value per generated graph/cell."""
    keys = [
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
    metrics = [metric for metric in METRICS if metric in frame.columns]
    return frame.groupby(keys, dropna=False, as_index=False)[metrics].mean(numeric_only=True)


def t_summary(values: pd.Series) -> tuple[int, float, float, float, float]:
    """Return n, mean, lower/upper 95% Student-t limits, and half-width."""
    array = values.dropna().to_numpy(float)
    n = len(array)
    if n == 0:
        return 0, np.nan, np.nan, np.nan, np.nan
    mean = float(array.mean())
    if n < 2:
        return n, mean, np.nan, np.nan, np.nan
    standard_error = float(array.std(ddof=1) / np.sqrt(n))
    critical = float(student_t.ppf(0.975, n - 1))
    halfwidth = critical * standard_error
    return n, mean, mean - halfwidth, mean + halfwidth, halfwidth


def paired_table(
    graph_frame: pd.DataFrame,
    *,
    axis: str,
    left,
    right,
    hold: list[str],
    label: str,
) -> pd.DataFrame:
    """Form a paired contrast along one design axis while holding the rest fixed."""
    keys = BASE_KEYS + hold
    metrics = [metric for metric in METRICS if metric in graph_frame.columns]

    left_frame = graph_frame[graph_frame[axis] == left]
    right_frame = graph_frame[graph_frame[axis] == right]
    left_frame = left_frame[keys + metrics].rename(
        columns={metric: f"{metric}_left" for metric in metrics}
    )
    right_frame = right_frame[keys + metrics].rename(
        columns={metric: f"{metric}_right" for metric in metrics}
    )
    merged = left_frame.merge(
        right_frame,
        on=keys,
        how="inner",
        validate="one_to_one",
    )

    group_keys = [key for key in keys if key != "seed"]
    rows = []
    for group_value, group in merged.groupby(group_keys, dropna=False):
        group_value = group_value if isinstance(group_value, tuple) else (group_value,)
        row = dict(zip(group_keys, group_value))
        row.update(
            {
                "contrast": label,
                "left": left,
                "right": right,
                "paired_seeds": int(group["seed"].nunique()),
            }
        )
        for metric in metrics:
            delta = group[f"{metric}_right"] - group[f"{metric}_left"]
            n, mean, low, high, halfwidth = t_summary(delta)
            row[f"{metric}_delta_mean"] = mean
            row[f"{metric}_delta_lo95"] = low
            row[f"{metric}_delta_hi95"] = high
            row[f"{metric}_delta_halfwidth95"] = halfwidth
            row[f"{metric}_paired_n"] = n
        rows.append(row)
    return pd.DataFrame(rows)


def main() -> int:
    """Compute the registered paired contrasts and write auditable analysis outputs."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("results", help="Path to an experiment results.csv file.")
    parser.add_argument("--out", required=True, help="Output paired-contrast CSV path.")
    args = parser.parse_args()

    raw = pd.read_csv(args.results)
    if "cell_status" in raw.columns:
        raw = raw[raw["cell_status"] == "complete"].copy()
    graph_frame = graph_level(raw)

    tables: list[pd.DataFrame] = []

    # Superlinear versus linear sample scaling, holding mask and alpha fixed.
    if set(graph_frame["gamma"].unique()) >= {1.0, 1.25}:
        tables.append(
            paired_table(
                graph_frame,
                axis="gamma",
                left=1.0,
                right=1.25,
                hold=["missingness_mode", "missing_rate_target", "alpha_schedule"],
                label="gamma_1.25_minus_1.0",
            )
        )

    # Missingness effects, holding sample scaling and alpha fixed.
    modes = set(graph_frame["missingness_mode"].astype(str))
    if {"complete", "self_masking_gaussian_preserving"} <= modes:
        tables.append(
            paired_table(
                graph_frame,
                axis="missingness_mode",
                left="complete",
                right="self_masking_gaussian_preserving",
                hold=["gamma", "alpha_schedule"],
                label="quadratic_minus_complete",
            )
        )
    if {"complete", "self_masking_logistic_population"} <= modes:
        tables.append(
            paired_table(
                graph_frame,
                axis="missingness_mode",
                left="complete",
                right="self_masking_logistic_population",
                hold=["gamma", "alpha_schedule"],
                label="logistic_minus_complete",
            )
        )

    # Fixed-alpha sensitivity, holding sample scaling and missingness fixed.
    schedules = set(graph_frame["alpha_schedule"].astype(str))
    if {"n_inverse_half", "fixed_005"} <= schedules:
        tables.append(
            paired_table(
                graph_frame,
                axis="alpha_schedule",
                left="n_inverse_half",
                right="fixed_005",
                hold=["gamma", "missingness_mode", "missing_rate_target"],
                label="fixed_005_minus_n_inverse_half",
            )
        )

    output = (
        pd.concat([table for table in tables if len(table)], ignore_index=True)
        if tables
        else pd.DataFrame()
    )
    output_path = Path(args.out)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output.to_csv(output_path, index=False)
    print(output.to_string(index=False, max_rows=40))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
