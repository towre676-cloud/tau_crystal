#!/usr/bin/env bash
set -euo pipefail; umask 022
base="analysis/morpho/packs"
strict=${STRICT_BOUNDARY:-1}
[ -d "$base" ] || { echo "[BOUNDARY] no $base"; exit 0; }
rc=0; scaffolded=0
for p in "$base"/run_*; do
  [ -d "$p" ] || continue
  b="$p/boundary.txt"; s="$p/boundary.sig"
  if [ ! -f "$b" ] || [ ! -f "$s" ]; then
    bash scripts/morpho/scaffold_boundary.sh "$p" || true
    scaffolded=1
  fi
  if [ -f "$b" ] && [ -f "$s" ]; then
    want=$(awk '{print $1}' "$s")
    have=$(sha256sum "$b" | awk '{print $1}')
    if [ "$want" != "$have" ]; then echo "[BOUNDARY] signature mismatch in $(basename "$p")"; rc=1; else echo "[BOUNDARY] ok $(basename "$p")"; fi
  else
    rc=1
  fi
done
if [ "$scaffolded" = "1" ] && [ "$strict" = "1" ]; then
  echo "[BOUNDARY] scaffold(s) created; STRICT_BOUNDARY=1 → failing"; rc=1
fi
exit $rc
