#!/usr/bin/env python3
"""Combine primary seeds 0--9 with extension seeds 10--19 for precision analysis."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import pandas as pd


def main() -> int:
    """Combine non-overlapping primary seed blocks into the registered 20-seed result set."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--primary-dir", required=True)
    parser.add_argument("--extra-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    args = parser.parse_args()

    primary = Path(args.primary_dir)
    extension = Path(args.extra_dir)
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)

    for directory in [primary, extension]:
        verification = directory / "verification.json"
        if not verification.exists() or not json.loads(verification.read_text()).get("pass", False):
            raise SystemExit(f"FAILED: verified input required: {verification}")

    first = pd.read_csv(primary / "results.csv", dtype={"cell_id": "string"})
    second = pd.read_csv(extension / "results.csv", dtype={"cell_id": "string"})
    ids_first = set(first.cell_id.astype(str))
    ids_second = set(second.cell_id.astype(str))
    overlap = ids_first & ids_second
    if overlap:
        raise SystemExit(f"FAILED overlapping graph-cell IDs: {list(sorted(overlap))[:5]}")

    seeds_first = set(first.seed.astype(int))
    seeds_second = set(second.seed.astype(int))
    if seeds_first & seeds_second:
        raise SystemExit(f"FAILED overlapping seeds: {sorted(seeds_first & seeds_second)}")

    combined = pd.concat([first, second], ignore_index=True, sort=False)
    combined.to_csv(output / "results.csv", index=False)
    report = {
        "pass": True,
        "primary_cells": len(ids_first),
        "extension_cells": len(ids_second),
        "combined_cells": len(ids_first | ids_second),
        "primary_seeds": sorted(seeds_first),
        "extension_seeds": sorted(seeds_second),
        "rows": len(combined),
        "purpose": "twenty-seed descriptive precision analysis; registered blocks remain separately verified",
    }
    (output / "combination_report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
