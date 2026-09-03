#!/usr/bin/env bash
# Install the exact public Python environment used for reproduction.
set -Eeuo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

SYSTEM_PACKAGES=(
  python3 python3-venv python3-pip python3-dev build-essential ca-certificates
  tar gzip coreutils libgomp1 poppler-utils fonts-tinos
)

if ! command -v apt-get >/dev/null 2>&1; then
  echo "ERROR: this zero-setup script supports Ubuntu/Debian systems with apt-get." >&2
  exit 70
fi

missing=()
for pkg in "${SYSTEM_PACKAGES[@]}"; do
  dpkg-query -W -f='${Status}' "$pkg" 2>/dev/null | grep -q '^install ok installed$' || missing+=("$pkg")
done
if ((${#missing[@]})); then
  if [[ "$(id -u)" -eq 0 ]]; then
    env DEBIAN_FRONTEND=noninteractive apt-get update
    env DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends "${missing[@]}"
  else
    command -v sudo >/dev/null 2>&1 || { echo "ERROR: sudo is required to install system packages." >&2; exit 71; }
    sudo env DEBIAN_FRONTEND=noninteractive apt-get update
    sudo env DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends "${missing[@]}"
  fi
fi

python3 - <<'PY'
import sys
if sys.version_info < (3, 11):
    raise SystemExit(f"Python >=3.11 is required; found {sys.version.split()[0]}")
print("Python:", sys.version.split()[0])
PY

if [[ ! -x .venv/bin/python ]]; then
  python3 -m venv .venv
fi
source .venv/bin/activate
python -m pip install -r requirements-lock.txt

python - <<'PY'
from importlib.metadata import PackageNotFoundError, version
from pathlib import Path
problems=[]
for raw in Path('requirements-lock.txt').read_text().splitlines():
    line=raw.strip()
    if not line or line.startswith('#'): continue
    name,want=line.split('==',1)
    try: got=version(name.strip())
    except PackageNotFoundError: got='missing'
    if got != want.strip(): problems.append((name.strip(),want.strip(),got))
if problems:
    raise SystemExit(f"Pinned dependency mismatch: {problems}")
print("Pinned Python dependencies: PASS")
PY

bash scripts/check_compute_environment.sh
