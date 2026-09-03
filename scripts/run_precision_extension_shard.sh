#!/usr/bin/env bash
# Run seeds 10--19 for the registered primary-scaling precision extension.
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
"$PYTHON" -m pytest -q tests

out="results/primary_scaling_precision_extension_shard${IDX}"
"$PYTHON" code/experiments/run_recovery_experiments.py \
  --config configs/primary_scaling_precision_extension.yaml \
  --output-dir "$out" \
  --n-jobs "$N_JOBS" --trace-mode summary \
  --num-shards 4 --shard-index "$IDX" --fail-fast

"$PYTHON" - "$out" <<'PY'
import sys
from pathlib import Path

import pandas as pd

output_dir = Path(sys.argv[1])
results = pd.read_csv(output_dir / "results.csv", dtype={"cell_id": "string"})
status = results["cell_status"].fillna("complete").astype(str)
completed_ids = set(
    results.loc[status == "complete", "cell_id"].dropna().astype(str)
)
failed_rows = int((status != "complete").sum())
if len(completed_ids) != 255 or failed_rows:
    raise SystemExit(
        f"{output_dir}: expected 255 complete cells; "
        f"observed {len(completed_ids)}, failed rows={failed_rows}"
    )
print(f"{output_dir}: PASS (255/255 graph cells)")
PY
