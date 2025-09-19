#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
err_json(){ printf '%s\n' "{\"metric\":\"error\",\"msg\":\"$1\",\"accept\":0}"; }
set -E -o pipefail; set +H; umask 022

# Usage:
#   predicates.sh symmetry  <left.tsv> <right.tsv> <epsilon>
#   predicates.sh stability <A_t1.tsv> <A_t2.tsv> <delta>
#   predicates.sh similar   <A.tsv>   <B.tsv>   <tau>

fn="${1:-}"; A="${2:-}"; B="${3:-}"; P="${4:-}"
[ -n "$fn" ] || { echo "missing fn"; exit 2; }
symmetry(){ L="$1"; R="$2"; EPS="$3"; [ -s "$L" ] && [ -s "$R" ] && [ -n "$EPS" ] || { err_json "missing or empty input"; exit 2; }
RMS=$(paste "$L" "$R" | awk -F"\t" '{if($1 ~ /^#/ || $3 ~ /^#/)next; if(NF<4)next; xL=$1+0; yL=$2+0; xR=-($3+0); yR=$4+0; dx=xL-xR; dy=yL-yR; s+=dx*dx+dy*dy; n++} END{if(n==0){print "NaN"}else{printf("%.8f", sqrt(s/n))}}')
acc=$(awk -v r="$RMS" -v e="$EPS" 'BEGIN{print (r<=e)?1:0}')
printf "%s\n" "{\"metric\":\"symmetry_RMS\",\"value\":$RMS,\"epsilon\":$EPS,\"accept\":$acc}"
}
stability(){ T1="$1"; T2="$2"; DEL="$3"; [ -s "$T1" ] && [ -s "$T2" ] && [ -n "$DEL" ] || { err_json "missing or empty input"; exit 2; }
F=$(paste "$T1" "$T2" | awk -F"\t" '{if($1 ~ /^#/ || $3 ~ /^#/)next; if(NF<4)next; dx=$1-$3; dy=$2-$4; s+=dx*dx+dy*dy} END{if(s==0){print "0.00000000"}else{printf("%.8f", sqrt(s))}}')
acc=$(awk -v f="$F" -v d="$DEL" 'BEGIN{print (f<=d)?1:0}')
printf "%s\n" "{\"metric\":\"stability_F\",\"value\":$F,\"delta\":$DEL,\"accept\":$acc}"
}
similar(){ X="$1"; Y="$2"; TAU="$3"; [ -s "$X" ] && [ -s "$Y" ] && [ -n "$TAU" ] || { err_json "missing or empty input"; exit 2; }
RMS=$(paste "$X" "$Y" | awk -F"\t" '{if($1 ~ /^#/ || $3 ~ /^#/)next; if(NF<4)next; dx=$1-$3; dy=$2-$4; s+=dx*dx+dy*dy; n++} END{if(n==0){print "NaN"}else{printf("%.8f", sqrt(s/n))}}')
acc=$(awk -v r="$RMS" -v t="$TAU" 'BEGIN{print (r<=t)?1:0}')
printf "%s\n" "{\"metric\":\"similar_RMS\",\"value\":$RMS,\"tau\":$TAU,\"accept\":$acc}"
}
case "$fn" in symmetry) symmetry "$A" "$B" "$P";; stability) stability "$A" "$B" "$P";; similar) similar "$A" "$B" "$P";; *) echo "unknown"; exit 2;; esac
