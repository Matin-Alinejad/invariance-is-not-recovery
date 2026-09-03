#!/usr/bin/env bash
# Compile all three pinned formal corroboration projects.
set -euo pipefail
root="$(cd "$(dirname "$0")" && pwd)"
for project in recovery student_t information; do
  echo "==> formal/$project"
  (cd "$root/$project" && lake build)
done
echo "All formal components compiled successfully."
