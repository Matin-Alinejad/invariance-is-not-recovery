#!/usr/bin/env bash
# Report the reference compute profile used for the Python campaign.
set -Eeuo pipefail

REFERENCE_CPUS=32
REFERENCE_RAM_GB=64
REFERENCE_DISK_GB=200

cpus="$(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN)"
ram_gb="$(awk '/MemTotal/ {printf "%.1f", $2/1024/1024}' /proc/meminfo 2>/dev/null || echo unknown)"
disk_gb="$(df -BG . | awk 'NR==2 {gsub(/G/,"",$2); print $2}')"

echo "Reference VM: Ubuntu, 32 vCPU, 64 GB RAM, 200 GB disk."
echo "Detected environment: ${cpus} CPU threads, ${ram_gb} GB RAM, ${disk_gb} GB filesystem size."

if [[ "$cpus" =~ ^[0-9]+$ ]] && (( cpus < REFERENCE_CPUS )); then
  echo "NOTE: fewer CPUs are available than in the reference VM; results remain valid but runtime will increase."
fi
