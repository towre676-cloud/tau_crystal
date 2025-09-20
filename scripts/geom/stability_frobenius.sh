#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
A_t1="${1:-}"; A_t2="${2:-}"; delta="${3:-0.02}"
[ -f "$A_t1" ] && [ -f "$A_t2" ] || { echo "usage: A_t1.tsv A_t2.tsv delta" >&2; exit 1; }
tmp1=$(mktemp); tmp2=$(mktemp)
scripts/geom/canonicalize_tsv.sh "$A_t1" "$tmp1"
scripts/geom/canonicalize_tsv.sh "$A_t2" "$tmp2"
paste "$tmp1" "$tmp2" | awk -v delta="$delta" '{dx=$1-$3; dy=$2-$4; s+=dx*dx+dy*dy; n++} END{if(n==0){print "NaN"; exit 2} frob=sqrt(s); print (frob<delta?"TRUE":"FALSE")"\t"frob"\t"delta }'
rm -f "$tmp1" "$tmp2"
