#!/usr/bin/env python3
"""Summarize graph-level recovery metrics with Student-t confidence intervals."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
import pandas as pd
from scipy.stats import t as student_t

GROUP_COLUMNS = [
    "evaluation_scope",
    "topology",
    "p",
    "gamma",
    "missingness_mode",
    "missing_rate_target",
    "alpha_schedule",
]
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
    "oracle_separator_coverage_fraction",
    "oracle_pc_dependent_partial_corr_q05",
]


def ci95(values) -> tuple[float, float, float]:
    """Return the mean and two-sided 95% Student-t confidence interval."""
    array = np.asarray(pd.Series(values).dropna(), float)
    if len(array) == 0:
        return np.nan, np.nan, np.nan
    mean = float(array.mean())
    if len(array) < 2:
        return mean, np.nan, np.nan
    standard_error = float(array.std(ddof=1) / np.sqrt(len(array)))
    critical = float(student_t.ppf(0.975, df=len(array) - 1))
    return mean, mean - critical * standard_error, mean + critical * standard_error


def graph_level_frame(frame: pd.DataFrame) -> pd.DataFrame:
    """Use one independent observational unit per generated graph/cell.

    Whole-skeleton rows already contribute one row per graph. Target-restriction
    rows contain several targets from the same graph, so they are averaged within
    graph before uncertainty is computed across graph seeds. This prevents
    correlated target rows from being treated as independent Monte Carlo draws.
    """
    if "missing_rate_target" not in frame.columns:
        frame = frame.copy()
        frame["missing_rate_target"] = 0.0
    keys = ["cell_id", *GROUP_COLUMNS, "seed"]
    present_metrics = [metric for metric in METRICS if metric in frame.columns]
    return frame.groupby(keys, dropna=False, as_index=False)[present_metrics].mean(
        numeric_only=True
    )


def main() -> int:
    """Summarize graph-level recovery metrics and confidence intervals by registered condition."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("results", help="Path to an experiment results.csv file.")
    parser.add_argument("--out", required=True, help="Directory for summary outputs.")
    args = parser.parse_args()

    raw = pd.read_csv(args.results)
    if "cell_status" in raw.columns:
        failed_cells = int((raw["cell_status"] == "failed").sum())
        complete = raw[raw["cell_status"] == "complete"].copy()
    else:
        failed_cells = 0
        complete = raw.copy()

    graph_frame = graph_level_frame(complete)
    output_dir = Path(args.out)
    output_dir.mkdir(parents=True, exist_ok=True)

    rows = []
    for key, group in graph_frame.groupby(GROUP_COLUMNS, dropna=False):
        row = dict(zip(GROUP_COLUMNS, key))
        row["n_graph_cells"] = len(group)
        row["n_graph_seeds"] = group["seed"].nunique()
        for metric in METRICS:
            if metric not in group.columns:
                continue
            mean, low, high = ci95(group[metric])
            row[f"{metric}_mean"] = mean
            row[f"{metric}_lo95"] = low
            row[f"{metric}_hi95"] = high
            row[f"{metric}_halfwidth95"] = (
                (high - low) / 2 if np.isfinite(low) and np.isfinite(high) else np.nan
            )
        rows.append(row)

    summary = pd.DataFrame(rows).sort_values(GROUP_COLUMNS)
    summary.to_csv(output_dir / "summary.csv", index=False)

    checks = {
        "failed_cells": failed_cells,
        "nonfinite_f1": int((~np.isfinite(complete["f1"])).sum()),
        "deterministic_f1_bound_violations": int(
            (complete.get("deterministic_bound_verified", True) == False).sum()  # noqa: E712
        ),
        "same_sample_calibration_rows": (
            int((complete["mask_calibration"] != "population_fixed").sum())
            if "mask_calibration" in complete
            else len(complete)
        ),
        "same_realization_standardization_rows": (
            int(
                (
                    complete["data_standardization"]
                    != "none_dedicated_population_sem_raw"
                ).sum()
            )
            if "data_standardization" in complete
            else len(complete)
        ),
        "sanitizer_clipping_active_rows": (
            int((complete["ci_sanitizer_clipping_inactive"] == False).sum())  # noqa: E712
            if "ci_sanitizer_clipping_inactive" in complete
            else len(complete)
        ),
        "target_rows_treated_as_independent_for_ci": 0,
    }
    (output_dir / "data_quality_checks.json").write_text(
        json.dumps(checks, indent=2) + "\n"
    )

    print(summary.to_string(index=False, max_rows=30))
    print(json.dumps(checks, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
