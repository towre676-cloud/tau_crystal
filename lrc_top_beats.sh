#!/usr/bin/env sh
# Usage: ./lrc_top_beats.sh annotated.csv [N]
CSV="${1:-lrc_random_results_annotated.csv}"
N="${2:-10}"
awk -F, 'NR==1{next} {sn=$11+0; sd=$12+0; if (sd>0 && sn>0){val=sn/sd; print val "," $0}}' "$CSV" \
 | sort -t, -k1,1nr \
 | head -n "$N" \
 | cut -d, -f2-
