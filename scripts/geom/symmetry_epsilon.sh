#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
A="${1:-}"; B="${2:-}"; eps="${3:-0.01}"
[ -f "$A" ] && [ -f "$B" ] || { echo "FALSE\tNaN\t"$(printf "%s" "$eps"); exit 0; }
tA=$(mktemp); tB=$(mktemp)
scripts/geom/canonicalize_tsv.sh "$A" "$tA" || { echo "FALSE\tNaN\t$eps"; rm -f "$tA" "$tB"; exit 0; }
scripts/geom/canonicalize_tsv.sh "$B" "$tB" || { echo "FALSE\tNaN\t$eps"; rm -f "$tA" "$tB"; exit 0; }
paste "$tA" "$tB" | awk -v e="$eps" '
  { ax=$1; ay=$2; bx=(-$3); by=$4; dx=ax-bx; dy=ay-by; s+=dx*dx+dy*dy; n++ }
  END{ if(n==0){ print "FALSE\tNaN\t"e; exit 0 } rms=sqrt(s/n); print (rms<e?"TRUE":"FALSE")"\t"rms"\t"e }
'
rm -f "$tA" "$tB"
