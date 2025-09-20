#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
A="${1:-}"; B="${2:-}"; eps="${3:-0.01}"
[ -f "$A" ] && [ -f "$B" ] || { echo "usage: A.tsv B.tsv eps" >&2; exit 1; }
tmpA=$(mktemp); tmpB=$(mktemp)
scripts/geom/canonicalize_tsv.sh "$A" "$tmpA"
scripts/geom/canonicalize_tsv.sh "$B" "$tmpB"
paste "$tmpA" "$tmpB" | awk -v eps="$eps" '{ax=$1; ay=$2; bx=(-$3); by=$4; dx=ax-bx; dy=ay-by; s+=dx*dx+dy*dy; n++} END{if(n==0){print "NaN"; exit 2} rms=sqrt(s/n); print (rms<eps?"TRUE":"FALSE")"\t"rms"\t"eps }'
rm -f "$tmpA" "$tmpB"
