#!/usr/bin/env bash
set -euo pipefail; umask 022
base="analysis/morpho/packs"
strict=${STRICT_BOUNDARY:-0}
[ -d "$base" ] || { echo "[BOUNDARY] no $base"; exit 0; }
rc=0
for p in "$base"/run_*; do
  [ -d "$p" ] || continue
  if [ ! -f "$p/boundary.txt" ] || [ ! -f "$p/boundary.sig" ]; then
    if [ "$strict" = "1" ]; then
      echo "[BOUNDARY] missing boundary in $p (STRICT)"; rc=1
    else
      bash scripts/morpho/scaffold_boundary.sh "$p" || rc=1
    fi
  fi
  # verify signature matches
  if [ -f "$p/boundary.txt" ] && [ -f "$p/boundary.sig" ]; then
    want=$(awk '{print $1}' "$p/boundary.sig")
    have=$(sha256sum "$p/boundary.txt" | awk '{print $1}')
    if [ "$want" != "$have" ]; then
      echo "[BOUNDARY] signature mismatch in $p"; rc=1
    else
      echo "[BOUNDARY] ok $(basename "$p")"
    fi
  fi
done
exit $rc
