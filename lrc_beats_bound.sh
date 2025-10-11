#!/usr/bin/env sh
# Usage: ./lrc_beats_bound.sh annotated.csv
CSV="${1:-lrc_random_results_annotated.csv}"
awk -F, 'NR==1{print; next} {sn=$11+0; sd=$12+0; if (sd>0 && sn>0) print}' "$CSV"
