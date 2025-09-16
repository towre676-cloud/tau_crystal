#!/usr/bin/env bash
set -E -o pipefail; set +H
in="${1:-.tau_ledger/langlands/ap_stable.json}"
out="analysis/micro_conductor.tsv"
mkdir -p analysis
if ! command -v jq >/dev/null 2>&1; then echo "[conductor] jq not found"; : > "$out"; exit 0; fi
jq -r '.hecke_eigenvalues | to_entries[] | "\(.key) \(.value)"' "$in" |
awk 'function log10(x){return log(x)/log(10)} {ap=($2<0?-$2:$2); if(ap<=0)next; lp=log10(ap); n++; s+=lp; s2+=lp*lp} END{if(n<2){print "variance_log_ap\t0.0"; print "micro_conductor_proxy\t0"; exit} var=(s2-s*s/n)/(n-1); printf "variance_log_ap\t%.12f\nmicro_conductor_proxy\t%d\n", var, int(var*1000000)}' > "$out"
echo "[conductor] wrote $out"
