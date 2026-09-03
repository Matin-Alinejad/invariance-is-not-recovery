#!/usr/bin/env bash
# Exercise the dedicated target-local search branch on matched graph/sample conditions.
set -Eeuo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
PYTHON="${PYTHON:-python3}"
export PYTHONPATH="$ROOT/code${PYTHONPATH:+:$PYTHONPATH}"
rm -rf results/matched_local_global_smoke
"$PYTHON" code/experiments/run_recovery_experiments.py \
  --config configs/matched_local_global_smoke.yaml \
  --output-dir results/matched_local_global_smoke \
  --fresh --n-jobs 1 --trace-mode summary --fail-fast
"$PYTHON" - <<'PY'
import numpy as np
import pandas as pd

results = pd.read_csv("results/matched_local_global_smoke/results.csv")
if results["cell_id"].nunique() != 3:
    raise SystemExit(
        f"Expected 3 graph cells; observed {results['cell_id'].nunique()}"
    )

observed_scopes = results["evaluation_scope"].value_counts().to_dict()
expected_scopes = {
    "global_whole_skeleton": 3,
    "target_restriction_of_global": 12,
    "dedicated_local": 12,
}
for scope, expected_rows in expected_scopes.items():
    if observed_scopes.get(scope) != expected_rows:
        raise SystemExit((observed_scopes, expected_scopes))

local_rows = results[results.evaluation_scope == "dedicated_local"]
for metric in ["f1", "precision", "recall"]:
    if not np.isfinite(local_rows[metric]).all():
        raise SystemExit(f"Non-finite dedicated-local {metric}")
print(
    f"Dedicated-local smoke: PASS (3 graph cells, {len(local_rows)} local rows, "
    f"{results.shape[1]} columns)"
)
PY
