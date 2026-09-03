#!/usr/bin/env bash
# Recompute the structural, population-margin, and oracle diagnostics used by the released analysis.
set -Eeuo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
PYTHON="${PYTHON:-python3}"
N_JOBS="${N_JOBS:-8}"
export PYTHONPATH="$ROOT/code${PYTHONPATH:+:$PYTHONPATH}"
mkdir -p results/diagnostics

"$PYTHON" code/scripts/measure_structural_scope.py \
  --config configs/primary_scaling.yaml \
  --csv results/diagnostics/depth_scope.csv \
  --json results/diagnostics/depth_scope.json --n-jobs "$N_JOBS"
"$PYTHON" code/scripts/measure_population_margins.py \
  --config configs/primary_scaling.yaml \
  --csv results/diagnostics/population_margins.csv \
  --json results/diagnostics/population_margins.json --n-jobs "$N_JOBS"
"$PYTHON" code/scripts/measure_p20_oracle_queries.py \
  --config configs/primary_scaling.yaml \
  --csv results/diagnostics/p20_oracle_queries.csv \
  --json results/diagnostics/p20_oracle_queries.json --n-jobs "$N_JOBS"
"$PYTHON" code/scripts/verify_selection_identity.py \
  --output results/diagnostics/selection_identity_verification.json
"$PYTHON" code/scripts/stress_test_oracle_search.py \
  --output results/diagnostics/oracle_search_stress_test.json

echo "STRUCTURAL AND POPULATION DIAGNOSTICS: PASS"
