#!/usr/bin/env bash
set -e; set -o pipefail; set +H; umask 022; export LC_ALL=C LANG=C
spec="${1:-artifacts/curvature/curvature.tsv}"
col="${2:-1}"
out="${3:-artifacts/residue/zeta_residue.tsv}"
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
if [ ! -f "$spec" ]; then echo "[err] spectrum not found: $spec" >&2; exit 2; fi
# finite-rank surrogate: λ_i > 0 extracted from TSV column -> ζ(s)=∑ λ_i^{-s}, so −ζ′(0)=∑ ln λ_i
awk -v c="$col" 'NR==1{next} {v=$c+0; if(v>0){s+=log(v); n+=1; if(v<m || m==0) m=v; if(v>M) M=v}} END{if(n==0){print "n=0"; exit 3} printf "n\tlogdet\tlambda_min\tlambda_max\n%d\t%.9f\t%.9g\t%.9g\n",n,s,m,M}' "$spec" > "$tmp"
mkdir -p "$(dirname "$out")" || :
mv "$tmp" "$out"
echo "[ok] zeta-residue surrogate -> $out"
