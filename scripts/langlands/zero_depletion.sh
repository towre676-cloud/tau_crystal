#!/usr/bin/env bash
set -E -o pipefail; set +H
ords="${1:-analysis/double_zero_ords.tsv}"
out="analysis/zero_depletion.tsv"
[ -s "$ords" ] || { echo "[depletion] no ord file: $ords"; : > "$out"; exit 0; }
# eps in micro-units (default 1000 = 1e-3 of the micro interval)
eps="${EPS_MICRO:-1000}"
awk -F'\t' -v eps="$eps" 'BEGIN{for(k=0;k<=20;k++)bin[k]=0}
     NR>1{t=int(($2+500000)/eps); if(t>=0&&t<=20) bin[t]++}
     END{for(k=0;k<=20;k++) printf "%.6f\t%d\n", k*eps/1e6, bin[k]}' "$ords" > "$out"
echo "[depletion] wrote $out (bins of ${eps} micro)"
