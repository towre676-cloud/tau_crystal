#!/usr/bin/env bash
set -E -o pipefail; set +H
in="${1:-.tau_ledger/langlands/ap_stable.json}"
out="analysis/micro_conductor.tsv"
mkdir -p analysis
if ! command -v jq >/dev/null 2>&1; then echo "[conductor] jq not found"; printf "variance_log_ap\t0.0\nmicro_conductor_proxy\t0\n" > "$out"; exit 0; fi
if [ ! -s "$in" ] || ! jq -e 'has("hecke_eigenvalues") and (.hecke_eigenvalues|type=="object" and (.|length>0))' "$in" >/dev/null 2>&1; then
  printf "variance_log_ap\t0.0\nmicro_conductor_proxy\t0\n" > "$out"; echo "[conductor] no data in $in"; exit 0
fi
jq -r '.hecke_eigenvalues | to_entries[] | "\(.key)\t\(.value)"' "$in" |
awk -F"\t" 'function log10(x){return log(x)/log(10)} {ap=($2<0?-$2:$2); if(ap<=0)next; lp=log10(ap); n++; s+=lp; s2+=lp*lp} END{if(n<2){print "variance_log_ap\t0.0\nmicro_conductor_proxy\t0"; exit} var=(s2-s*s/n)/(n-1); printf "variance_log_ap\t%.12f\nmicro_conductor_proxy\t%d\n", var, int(var*1000000)}' > "$out"
echo "[conductor] wrote $out"
