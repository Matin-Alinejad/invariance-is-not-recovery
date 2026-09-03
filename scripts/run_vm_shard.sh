#!/usr/bin/env bash
# Run one quarter of every mandatory experiment block on a reference-style VM.
set -Eeuo pipefail
IDX="${1:-}"
N_JOBS="${N_JOBS:-8}"
[[ "$IDX" =~ ^[0-3]$ ]] || { echo "Usage: $0 <0|1|2|3>" >&2; exit 2; }

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/setup_ubuntu_vm.sh
source .venv/bin/activate
export PYTHONPATH="$ROOT/code${PYTHONPATH:+:$PYTHONPATH}"
PYTHON="${PYTHON:-python}"

LOG_DIR="$ROOT/results/logs/server_${IDX}"
mkdir -p "$LOG_DIR"
LOG_FILE="$LOG_DIR/run_$(date -u +%Y%m%dT%H%M%SZ).log"
exec > >(tee -a "$LOG_FILE") 2>&1

echo "Reference campaign hardware: Ubuntu VM, 32 vCPU, 64 GB RAM, 200 GB disk."
echo "Python workers used by the reference campaign: $N_JOBS"
echo "Shard index: $IDX of 4"

"$PYTHON" -m pytest -q tests

if [[ "$IDX" == "0" ]]; then
  bash scripts/run_global_smoke.sh
fi

run_block() {
  local label="$1" config="$2" stem="$3" expected="$4"
  local out="results/${stem}_shard${IDX}"
  echo "Running ${label}: expected ${expected} graph cells on shard ${IDX}."
  "$PYTHON" code/experiments/run_recovery_experiments.py \
    --config "$config" \
    --output-dir "$out" \
    --n-jobs "$N_JOBS" \
    --trace-mode summary \
    --num-shards 4 \
    --shard-index "$IDX" \
    --fail-fast
  "$PYTHON" - "$out" "$expected" <<'PY'
import sys
from pathlib import Path

import pandas as pd

output_dir = Path(sys.argv[1])
expected_cells = int(sys.argv[2])
results = pd.read_csv(output_dir / "results.csv", dtype={"cell_id": "string"})
status = results["cell_status"].fillna("complete").astype(str)
completed = results[status == "complete"]
completed_ids = set(completed["cell_id"].dropna().astype(str))
failed_rows = int((status != "complete").sum())
if len(completed_ids) != expected_cells or failed_rows:
    raise SystemExit(
        f"{output_dir}: expected {expected_cells} complete graph cells; "
        f"observed {len(completed_ids)}, failed rows={failed_rows}"
    )

failures_path = output_dir / "failures.csv"
if failures_path.exists() and failures_path.stat().st_size:
    failures = pd.read_csv(failures_path)
    if len(failures):
        raise SystemExit(
            f"{output_dir}: failures.csv contains {len(failures)} rows"
        )
print(f"{output_dir}: PASS ({len(completed_ids)}/{expected_cells} graph cells)")
PY
}

run_block "primary scaling" configs/primary_scaling.yaml primary_scaling 255
run_block "significance-threshold sensitivity" configs/significance_threshold_sensitivity.yaml significance_threshold_sensitivity 90
run_block "retention sensitivity" configs/retention_sensitivity.yaml retention_sensitivity 30
run_block "matched local/global" configs/matched_local_global.yaml matched_local_global 60

cat > "results/server_${IDX}_completion.json" <<EOF
{"server_index": ${IDX}, "python_workers": ${N_JOBS}, "primary_scaling_cells": 255, "significance_threshold_cells": 90, "retention_cells": 30, "matched_local_global_cells": 60, "pass": true}
EOF

echo "SERVER ${IDX}: ALL MANDATORY SHARDS COMPLETE"
