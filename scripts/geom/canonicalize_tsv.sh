#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
in="${1:-}"; out="${2:-/dev/stdout}"
[ -f "$in" ] || { echo "missing input TSV" >&2; exit 1; }
awk 'NF>=2{n++; x+=$1; y+=$2; xs+=$1*$1; ys+=$2*$2; print > "/tmp/can_raw.$$"} END{if(n==0)exit 1; mx=x/n; my=y/n; rx=sqrt(xs/n - mx*mx); ry=sqrt(ys/n - my*my); if(rx==0)rx=1; if(ry==0)ry=1; }' "$in" >/dev/null
awk -v OFS="\t" 'NR==FNR{next} {print ($1-mx)/rx, ($2-my)/ry}' /dev/null /tmp/can_raw.$$ 2>/dev/null | awk 'BEGIN{mx=0;my=0;rx=1;ry=1}{print $0}' > "$out"
rm -f "/tmp/can_raw.$$"
