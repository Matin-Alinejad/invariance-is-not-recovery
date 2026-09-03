#!/usr/bin/env python3
"""Assess Monte Carlo F1 precision using graph cells as independent replications."""
from __future__ import annotations

import argparse
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


def graph_level_f1(frame: pd.DataFrame) -> pd.DataFrame:
    """Average correlated target rows within each generated graph before inference."""
    if "missing_rate_target" not in frame.columns:
        frame = frame.copy()
        frame["missing_rate_target"] = 0.0
    keys = ["cell_id", *GROUP_COLUMNS, "seed"]
    return frame.groupby(keys, dropna=False, as_index=False)["f1"].mean()


def main() -> int:
    """Evaluate Monte Carlo confidence-interval precision for registered condition groups."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("results", help="Path to an experiment results.csv file.")
    parser.add_argument(
        "--f1-halfwidth",
        type=float,
        default=0.05,
        help="Maximum acceptable two-sided 95%% F1 half-width (default: 0.05).",
    )
    parser.add_argument("--out", required=True, help="Output CSV path.")
    args = parser.parse_args()

    raw = pd.read_csv(args.results)
    if "cell_status" in raw.columns:
        raw = raw[raw["cell_status"] == "complete"].copy()

    graph_level = graph_level_f1(raw)
    rows = []
    for key, group in graph_level.groupby(GROUP_COLUMNS, dropna=False):
        values = group["f1"].dropna().to_numpy(float)
        if len(values) < 2:
            halfwidth = np.inf
        else:
            critical = float(student_t.ppf(0.975, df=len(values) - 1))
            halfwidth = critical * values.std(ddof=1) / np.sqrt(len(values))
        rows.append(
            {
                **dict(zip(GROUP_COLUMNS, key)),
                "n_graph_cells": len(values),
                "f1_halfwidth95": halfwidth,
                "needs_more_seeds": bool(halfwidth > args.f1_halfwidth),
            }
        )

    output = pd.DataFrame(rows)
    output_path = Path(args.out)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output.to_csv(output_path, index=False)

    print(output[output["needs_more_seeds"]].to_string(index=False))
    print(
        "cells needing more precision:",
        int(output["needs_more_seeds"].sum()),
        "/",
        len(output),
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
