#!/usr/bin/env bash
# Merge seeds 10--19 and combine them with primary seeds 0--9 for precision summaries.
set -Eeuo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
[[ -x .venv/bin/python ]] || bash scripts/setup_ubuntu_vm.sh
source .venv/bin/activate
PYTHON="${PYTHON:-python}"
export PYTHONPATH="$ROOT/code${PYTHONPATH:+:$PYTHONPATH}"

PRIMARY_DIR="results/primary_scaling"
EXTENSION_DIR="results/primary_scaling_precision_extension"
COMBINED_DIR="results/primary_scaling_20_seeds"
rm -rf "$EXTENSION_DIR" "$COMBINED_DIR"

"$PYTHON" code/scripts/merge_shards.py \
  --input-dir results/primary_scaling_precision_extension_shard0 \
  --input-dir results/primary_scaling_precision_extension_shard1 \
  --input-dir results/primary_scaling_precision_extension_shard2 \
  --input-dir results/primary_scaling_precision_extension_shard3 \
  --output-dir "$EXTENSION_DIR"
"$PYTHON" code/scripts/verify_merged_results.py \
  --config configs/primary_scaling_precision_extension.yaml \
  --results-dir "$EXTENSION_DIR" --out "$EXTENSION_DIR/verification.json"

"$PYTHON" code/scripts/combine_primary_seed_blocks.py \
  --primary-dir "$PRIMARY_DIR" --extra-dir "$EXTENSION_DIR" --output-dir "$COMBINED_DIR"
"$PYTHON" analysis/summarize_recovery_results.py "$COMBINED_DIR/results.csv" --out "$COMBINED_DIR/analysis"
"$PYTHON" analysis/evaluate_monte_carlo_precision.py "$COMBINED_DIR/results.csv" \
  --f1-halfwidth 0.05 --out "$COMBINED_DIR/analysis/monte_carlo_precision.csv"
"$PYTHON" analysis/compute_paired_contrasts.py "$COMBINED_DIR/results.csv" \
  --out "$COMBINED_DIR/analysis/paired_contrasts_20_seeds_descriptive.csv"

"$PYTHON" - <<'PY'
import pandas as pd
x=pd.read_csv('results/primary_scaling_20_seeds/analysis/monte_carlo_precision.csv')
n=int(x.needs_more_seeds.astype(bool).sum())
print(f"Twenty-seed precision assessment: {len(x)} groups; {n} groups above 0.05 half-width")
if n: raise SystemExit("The registered precision extension did not close the 0.05 half-width criterion.")
PY

echo "PRIMARY PRECISION EXTENSION: PASS"
