#!/usr/bin/env python3
"""Compare reconstructed processed evidence with the released reference evidence."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parents[1]
NUMERIC_TOLERANCE = 1e-12


def _compare_csv(reference: Path, candidate: Path) -> str | None:
    left = pd.read_csv(reference)
    right = pd.read_csv(candidate)
    if left.shape != right.shape or list(left.columns) != list(right.columns):
        return "shape/schema differs"

    for column in left.columns:
        if pd.api.types.is_numeric_dtype(left[column]) and pd.api.types.is_numeric_dtype(
            right[column]
        ):
            x = left[column].to_numpy(float)
            y = right[column].to_numpy(float)
            if not np.array_equal(np.isnan(x), np.isnan(y)):
                return f"{column}: NaN pattern differs"
            finite = np.isfinite(x) & np.isfinite(y)
            if finite.any() and float(np.max(np.abs(x[finite] - y[finite]))) > NUMERIC_TOLERANCE:
                return f"{column}: numeric difference > {NUMERIC_TOLERANCE:g}"
        elif not left[column].fillna("<NA>").astype(str).equals(
            right[column].fillna("<NA>").astype(str)
        ):
            return f"{column}: text differs"
    return None


def main() -> int:
    """Compare a reconstructed evidence bundle against the released evidence file by file."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--candidate", required=True, help="Fresh evidence directory.")
    parser.add_argument(
        "--reference",
        default=str(ROOT / "evidence"),
        help="Released evidence directory (default: evidence/).",
    )
    args = parser.parse_args()

    reference_root = Path(args.reference).resolve()
    candidate_root = Path(args.candidate).resolve()
    reference_files = sorted(
        path.relative_to(reference_root) for path in reference_root.rglob("*") if path.is_file()
    )
    candidate_files = sorted(
        path.relative_to(candidate_root) for path in candidate_root.rglob("*") if path.is_file()
    )

    problems: list[str] = []
    if reference_files != candidate_files:
        problems.append(
            f"file lists differ: reference={len(reference_files)}, "
            f"candidate={len(candidate_files)}"
        )

    for relative in sorted(set(reference_files) & set(candidate_files)):
        reference = reference_root / relative
        candidate = candidate_root / relative
        if relative.suffix == ".json":
            if json.loads(reference.read_text()) != json.loads(candidate.read_text()):
                problems.append(f"{relative}: JSON differs")
        elif relative.suffix == ".csv":
            issue = _compare_csv(reference, candidate)
            if issue:
                problems.append(f"{relative}: {issue}")
        elif reference.read_bytes() != candidate.read_bytes():
            problems.append(f"{relative}: bytes differ")

    if problems:
        print("EVIDENCE COMPARISON: FAIL")
        for problem in problems:
            print(" -", problem)
        return 2

    print(
        f"EVIDENCE COMPARISON: PASS ({len(reference_files)} files; "
        f"numeric tolerance {NUMERIC_TOLERANCE:g})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
