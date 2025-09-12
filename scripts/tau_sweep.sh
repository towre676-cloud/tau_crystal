#!/usr/bin/env bash
set +H; umask 022
in="${1:-.tau_ledger/signals/observable.tsv}"
run_id="${RUN_ID:-$(date -u +%Y%m%d-%H%M%S)}"
out=".tau_ledger/calibration/${run_id}.json"; mkdir -p ".tau_ledger/calibration"
[ -s "$in" ] || { echo "[err] missing observable series: $in" >&2; exit 2; }
gridK="8 16 32"; gridW="0.70 0.80 0.90 0.95"
bestS=99999999; bestK=0; bestW=0
tmp_series="$(mktemp)"; tmp_score="$(mktemp)"; trap "rm -f \"$tmp_series\" \"$tmp_score\"" EXIT
for K in $gridK; do
  for W in $gridW; do
    awk -v K="$K" -v W="$W" -f scripts/bin/ema_filter.awk "$in" > "$tmp_series" 2>/dev/null
    awk -f scripts/bin/score_series.awk "$tmp_series" > "$tmp_score" 2>/dev/null
    SVAL=99999998
    if [ -s "$tmp_score" ]; then read -r _ SVAL _ < "$tmp_score"; fi
    awk -v a="$SVAL" -v b="$bestS" "BEGIN{exit !(a<b)}" && { bestS="$SVAL"; bestK="$K"; bestW="$W"; }
  done
done
: > "$out"
printf "%s\n" "{" >> "$out"
printf "%s\n" "  \"schema\":\"taucrystal/calibration/v1\"," >> "$out"
printf "%s\n" "  \"tau_class\":\"spectral_or_work\"," >> "$out"
printf "%s\n" "  \"grid\":{\"K\":[8,16,32],\"omega\":[0.70,0.80,0.90,0.95]}," >> "$out"
printf "%s\n" "  \"choice\":{\"K\":$bestK,\"omega\":$bestW,\"score\":$bestS}," >> "$out"
if [ -f ".tau_ledger/operator.json" ]; then
  printf "%s" "  \"operator\":" >> "$out"; cat .tau_ledger/operator.json >> "$out"; printf "%s\n" "," >> "$out"
else
  printf "%s\n" "  \"operator\":{\"digest\":\"unknown\",\"size\":0,\"construction\":\"demo\"}," >> "$out"
fi
printf "%s\n" "  \"provenance\":{\"run_id\":\"$run_id\",\"host\":\"$(hostname)\",\"ts\":\"$(date -u +%Y-%m-%dT%H:%M:%SZ)\"}" >> "$out"
printf "%s\n" "}" >> "$out"
echo "$out"
