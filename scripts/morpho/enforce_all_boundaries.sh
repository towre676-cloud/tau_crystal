#!/usr/bin/env bash
set -euo pipefail; umask 022
base="analysis/morpho/packs"
[ -d "$base" ] || { echo "[BOUNDARY] no $base"; exit 0; }
rc=0
for p in "$base"/run_*; do
  [ -d "$p" ] || continue
  if [ -f "$p/boundary.txt" ] && [ -f "$p/boundary.sig" ]; then
    bash scripts/morpho/enforce_boundary.sh "$p" || rc=1
  else
    echo "[BOUNDARY] missing boundary in $p"; rc=1
  fi
done
exit $rc
