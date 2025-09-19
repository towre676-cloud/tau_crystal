#!/usr/bin/env bash
set -Eeuo pipefail
ledger=".tau_ledger/seq/tau.csv"
out=".tau_ledger/automorphic/new_zeros.json"
mkdir -p "$(dirname "$out")"
[ -s "$ledger" ] || { echo '{"zeros":[]}' > "$out"; exit 0; }
tmp="$(mktemp)"
awk -F, 'NR>1{print NR-1","$2}' "$ledger" > "$tmp"
# grid s ∈ {0.5,1.0,1.5,2.0,2.5}
awk -v OFS=',' '
BEGIN{ split("0.5 1.0 1.5 2.0 2.5",S," ") }
{ x=$1; y=$2; m+=y; c++; avg=m/c }
END{
  zeros=""; sep="";
  for(i in S){ s=S[i]; diff=(avg-1/s); if(diff*diff<1e-6){ zeros=zeros sep "{\"s\":"s",\"tau_mean\":"avg"}"; sep=","} }
  print "{\"zeros\":["zeros"]}"
}' "$tmp" > "$out"
rm -f "$tmp"; echo "$out"
