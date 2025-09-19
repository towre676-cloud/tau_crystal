#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
for d in $(ls -1dt analysis/morpho/packs/run_* 2>/dev/null); do
  [ -d "$d" ] || continue
  [ -f "$d/corridor.receipt.tsv" ] || continue
  [ -f "$d/global.L" ] || continue
  printf "%s\n" "$d"; exit 0
done
exit 1
