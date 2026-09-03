#!/usr/bin/env bash
# Run the public release verification suite from a clean repository checkout.
set -Eeuo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
PYTHON="${PYTHON:-python3}"
export PYTHONPATH="$ROOT/code${PYTHONPATH:+:$PYTHONPATH}"

"$PYTHON" -m pytest -q tests
"$PYTHON" analysis/verify_reported_results.py
"$PYTHON" analysis/verify_reference_artifacts.py
"$PYTHON" -m compileall -q code analysis run_experiments.py

# Every public Python command must expose a usable help surface.
for cli in \
  run_experiments.py \
  code/experiments/run_recovery_experiments.py \
  analysis/*.py \
  code/scripts/*.py; do
  "$PYTHON" "$cli" --help >/dev/null
done

for f in scripts/*.sh formal/build_all.sh; do bash -n "$f"; done

if grep -RniE '\b(sorry|admit)\b' formal --include='*.lean'; then
  echo 'ERROR: unfinished formal source found.' >&2
  exit 19
fi

find . -type d \( -name __pycache__ -o -name .pytest_cache \) -prune -exec rm -rf {} + || true
find . -type f \( -name '*.pyc' -o -name '*.pyo' \) -delete

# Public source must not contain machine-specific absolute development paths.
if grep -RniE '(^|[^[:alnum:]_])(/mnt/|/home/[^[:space:]]+/|[A-Za-z]:\\Users\\)' . \
  --exclude-dir=.venv --exclude-dir=results --exclude='*.pdf' --exclude='lake-manifest.json' --exclude='verify_release.sh'; then
  echo 'ERROR: machine-specific development path found.' >&2
  exit 20
fi

bash scripts/run_global_smoke.sh
bash scripts/run_target_local_smoke.sh

find . -type d \( -name __pycache__ -o -name .pytest_cache \) -prune -exec rm -rf {} + || true
find . -type f \( -name '*.pyc' -o -name '*.pyo' \) -delete

echo 'PUBLIC RELEASE VERIFICATION: PASS'
