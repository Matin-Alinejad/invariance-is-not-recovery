#!/usr/bin/env bash
# Reconstruct processed evidence, reported quantities, and reference artifacts from completed raw runs.
set -Eeuo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
PYTHON="${PYTHON:-python3}"
N_JOBS="${N_JOBS:-8}"
export PYTHONPATH="$ROOT/code${PYTHONPATH:+:$PYTHONPATH}"

for d in \
  results/primary_scaling \
  results/primary_scaling_20_seeds \
  results/significance_threshold_sensitivity \
  results/retention_sensitivity \
  results/matched_local_global; do
  [[ -f "$d/results.csv" ]] || { echo "Missing completed result block: $d/results.csv" >&2; exit 3; }
done

N_JOBS="$N_JOBS" bash scripts/run_structural_diagnostics.sh
"$PYTHON" analysis/reconstruct_evidence.py \
  --results-root results --diagnostics-dir results/diagnostics \
  --out results/reproduced_evidence
"$PYTHON" analysis/verify_evidence_reconstruction.py \
  --candidate results/reproduced_evidence
"$PYTHON" analysis/verify_reported_results.py \
  --evidence-dir results/reproduced_evidence \
  --out results/reproduced_reported_result_validation.md
"$PYTHON" analysis/verify_reference_artifacts.py \
  --evidence-dir results/reproduced_evidence \
  --output-dir results/reproduced_artifacts

echo "FULL REPRODUCTION FINALIZATION: PASS"
