#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
for d in $(ls -1dt analysis/morpho/packs/run_* 2>/dev/null); do
  [ -f "$d/corridor.receipt.tsv" ] && [ -f "$d/global.L" ] && { echo "$d"; exit 0; }
done; exit 1
