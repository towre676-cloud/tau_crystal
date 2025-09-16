#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
[ -s analysis/analytic_heegner.tsv ] || { echo "[rank] no analytic TSV"; exit 0; }
R=$(tail -n1 analysis/analytic_heegner.tsv | awk -F'\t' '{print $6+0}')
[ "$R" -ge 2 ] && exit 0 || exit 1
