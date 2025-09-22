#!/usr/bin/env bash
set -euo pipefail; set +H
IN="${1:-analysis/validation/tau_reference.csv}"
OUT="${2:-analysis/validation/tau_reference.tsv}"
if [ ! -s "$IN" ]; then echo "missing $IN"; exit 1; fi
printf "n\tkind\ttau\tone_plus_p11_mod_691\tnote\n" > "$OUT"
tail -n +2 "$IN" | awk -F, 'function modexp(b,e,m, r){r=1%m;b%=m;for(i=0;i<e;i++){r=(r*b)%m}return r} {n=$1; t=$2; note=$3; kind=(n==2||n==3||n==5||n==7||n==11||n==13||n==17||n==19||n==23||n==29||n==31||n==37)?"prime":"n"; mod=(n>1)?(1+modexp(n,11,691))%691:""; printf "%s\t%s\t%s\t%s\t%s\n", n, kind, t, mod, note}' >> "$OUT"
