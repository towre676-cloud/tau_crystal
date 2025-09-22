#!/usr/bin/env bash
set -euo pipefail; umask 022
d=".tau_ledger/langlands"
latest="$d/phase_next_latest.sha"
[ -f "$latest" ] || { echo "[PHASE] missing $latest"; exit 2; }
head=$(cat "$latest" | tr -d '\r\n')
best=$(LC_ALL=C ls "$d"/phase_next_*.sha 2>/dev/null | grep -v latest | sort -V | tail -n1 || true)
[ -n "$best" ] || { echo "[PHASE] no phase_next_*.sha"; exit 3; }
bestsha=$(cat "$best" | tr -d '\r\n')
if [ "$head" = "$bestsha" ]; then
  echo "[PHASE] ok latest matches head: $(basename "$best")"
else
  echo "[PHASE] mismatch: latest=$head head=$(basename "$best")=$bestsha"; exit 4
fi
