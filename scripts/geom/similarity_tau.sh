#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
A="${1:-}"; B="${2:-}"; tau="${3:-0.03}"
[ -f "$A" ] && [ -f "$B" ] || { echo "usage: A.tsv B.tsv tau" >&2; exit 1; }
tmpA=$(mktemp); tmpB=$(mktemp)
scripts/geom/canonicalize_tsv.sh "$A" "$tmpA"
scripts/geom/canonicalize_tsv.sh "$B" "$tmpB"
paste "$tmpA" "$tmpB" | awk -v tau="$tau" '{dx=$1-$3; dy=$2-$4; s+=dx*dx+dy*dy; n++} END{if(n==0){print "NaN"; exit 2} rms=sqrt(s/n); print (rms<tau?"TRUE":"FALSE")"\t"rms"\t"tau }'
rm -f "$tmpA" "$tmpB"
