#!/usr/bin/env bash
# Merge the four mandatory VM shards and reproduce all registered analyses.
set -Eeuo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
[[ -x .venv/bin/python ]] || bash scripts/setup_ubuntu_vm.sh
source .venv/bin/activate
PYTHON="${PYTHON:-python}"
export PYTHONPATH="$ROOT/code${PYTHONPATH:+:$PYTHONPATH}"

merge_block() {
  local stem="$1" config="$2" analysis_kind="$3"
  local out="results/$stem"
  rm -rf "$out"
  "$PYTHON" code/scripts/merge_shards.py \
    --input-dir "results/${stem}_shard0" \
    --input-dir "results/${stem}_shard1" \
    --input-dir "results/${stem}_shard2" \
    --input-dir "results/${stem}_shard3" \
    --output-dir "$out"
  "$PYTHON" code/scripts/verify_merged_results.py \
    --config "$config" --results-dir "$out" --out "$out/verification.json"
  "$PYTHON" analysis/summarize_recovery_results.py "$out/results.csv" --out "$out/analysis"
  "$PYTHON" analysis/evaluate_monte_carlo_precision.py "$out/results.csv" \
    --f1-halfwidth 0.05 --out "$out/analysis/monte_carlo_precision.csv"
  case "$analysis_kind" in
    paired)
      "$PYTHON" analysis/compute_paired_contrasts.py "$out/results.csv" \
        --out "$out/analysis/paired_contrasts.csv" ;;
    retention)
      "$PYTHON" analysis/compute_retention_and_local_contrasts.py "$out/results.csv" \
        --out-dir "$out/analysis" --kind retention ;;
    local)
      "$PYTHON" analysis/compute_retention_and_local_contrasts.py "$out/results.csv" \
        --out-dir "$out/analysis" --kind local ;;
  esac
}

merge_block primary_scaling configs/primary_scaling.yaml paired
merge_block significance_threshold_sensitivity configs/significance_threshold_sensitivity.yaml paired
merge_block retention_sensitivity configs/retention_sensitivity.yaml retention
merge_block matched_local_global configs/matched_local_global.yaml local

"$PYTHON" code/scripts/verify_cross_block_consistency.py \
  --primary results/primary_scaling \
  --alpha results/significance_threshold_sensitivity \
  --retention results/retention_sensitivity \
  --out results/cross_block_consistency.json

echo "MANDATORY CAMPAIGN MERGE AND ANALYSIS: PASS"
