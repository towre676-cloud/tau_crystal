#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
A_t1="${1:-}"; A_t2="${2:-}"; delta="${3:-0.02}"
[ -f "$A_t1" ] && [ -f "$A_t2" ] || { echo "FALSE\tNaN\t"$(printf "%s" "$delta"); exit 0; }
t1=$(mktemp); t2=$(mktemp)
scripts/geom/canonicalize_tsv.sh "$A_t1" "$t1" || { echo "FALSE\tNaN\t$delta"; rm -f "$t1" "$t2"; exit 0; }
scripts/geom/canonicalize_tsv.sh "$A_t2" "$t2" || { echo "FALSE\tNaN\t$delta"; rm -f "$t1" "$t2"; exit 0; }
awk -v d="$delta" '
  { if(NR==FNR){ ax[NR]=$1; ay[NR]=$2; next } dx=ax[FNR]-$1; dy=ay[FNR]-$2; s+=dx*dx+dy*dy; n++ }
  END{ if(n==0){ print "FALSE\tNaN\t"d; exit 0 } frob=sqrt(s); print (frob<d?"TRUE":"FALSE")"\t"frob"\t"d }
' "$t1" "$t2"
rm -f "$t1" "$t2"
