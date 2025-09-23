#!/usr/bin/env bash
set -euo pipefail; umask 022
strict="${STRICT_BOUNDARY:-1}"
rc=0
for dir in analysis/morpho/packs/run_*; do
  [ -d "$dir" ] || continue
  btxt="$dir/boundary.txt"; bsig="$dir/boundary.sig"
  if [ ! -f "$btxt" ] || [ ! -f "$bsig" ]; then
    scripts/gates/scaffold_boundary.sh "$dir" || true
    if [ "$strict" = "1" ]; then
      echo "[BOUNDARY] missing boundary in $(basename "$dir")"
      rc=2; continue
    fi
  fi
  # verify sig
  sha=$(sha256sum "$btxt" | awk '{print $1}')
  want=$(awk '{print $1}' "$bsig")
  if [ "$sha" != "$want" ]; then
    echo "[BOUNDARY] sig mismatch in $(basename "$dir")"
    rc=2; continue
  fi
  # reject placeholder if strict
  if [ "$strict" = "1" ] && grep -q '^#placeholder' "$btxt"; then
    echo "[BOUNDARY] placeholder present in $(basename "$dir") (STRICT)"
    rc=2; continue
  fi
  echo "[BOUNDARY] ok $(basename "$dir")"
done
exit "$rc"
