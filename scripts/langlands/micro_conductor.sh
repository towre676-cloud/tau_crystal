#!/usr/bin/env bash
set -E -o pipefail; set +H
in="${1:-.tau_ledger/langlands/ap_stable.json}"
out="analysis/micro_conductor.tsv"
emit_ap(){ if command -v jq >/dev/null 2>&1; then jq -r '.hecke_eigenvalues|to_entries[]|"\(.key) \(.value)"' "$1"; else sed -n 's/^[[:space:]]*"\([0-9]\+\)":[[:space:]]*\([-0-9.][0-9.eE+-]*\).*/\1 \2/p' "$1"; fi; }
[ -s "$in" ] || { echo "[conductor] no input: $in"; : > "$out"; exit 0; }
emit_ap "$in" | awk 'function log10(x){return log(x)/log(10)}
  {ap=$2+0; ap=(ap<0?-ap:ap); if(ap<=0) next; lp=log10(ap); n++; s+=lp; s2+=lp*lp}
  END{if(n<2){print "variance_log_ap\t0\nmicro_conductor_proxy\t0"; exit}
      var=(s2-s*s/n)/(n-1); printf "variance_log_ap\t%.9f\nmicro_conductor_proxy\t%d\n", var, int(var*1e6)}' > "$out"
echo "[conductor] wrote $out"
