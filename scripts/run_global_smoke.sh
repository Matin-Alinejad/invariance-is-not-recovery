#!/usr/bin/env bash
# Exercise the production global/restricted-global experiment path on six graph cells.
set -Eeuo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
PYTHON="${PYTHON:-python3}"
export PYTHONPATH="$ROOT/code${PYTHONPATH:+:$PYTHONPATH}"
rm -rf results/global_smoke
"$PYTHON" code/experiments/run_recovery_experiments.py \
  --config configs/global_smoke.yaml --output-dir results/global_smoke \
  --fresh --n-jobs 1 --trace-mode summary --fail-fast
"$PYTHON" code/scripts/verify_smoke_results.py \
  --results results/global_smoke/results.csv --out results/global_smoke/verification.json
"$PYTHON" - <<'PY'
import json
from pathlib import Path

import pandas as pd

results_path = Path("results/global_smoke/results.csv")
report_path = Path("results/global_smoke/verification.json")
results = pd.read_csv(results_path)
if results.shape[0] != 48:
    raise SystemExit(f"Expected 48 smoke rows; observed {results.shape[0]}")
if results["cell_id"].nunique() != 6:
    raise SystemExit(
        f"Expected 6 graph cells; observed {results['cell_id'].nunique()}"
    )
report = json.loads(report_path.read_text())
if report.get("pass") is not True:
    raise SystemExit(report)
print(
    f"Global smoke: PASS ({results.shape[0]} rows, "
    f"{results.shape[1]} columns, 6 graph cells)"
)
PY
