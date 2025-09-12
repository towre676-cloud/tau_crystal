#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
in="${1:-.tau_ledger/signals/observable.tsv}"
run_id="${RUN_ID:-$(date -u +%Y%m%d-%H%M%S)}"
out=".tau_ledger/calibration/${run_id}.json"; mkdir -p "$(dirname "$out")"
[ -s "$in" ] || { echo "[err] missing observable series: $in" >&2; exit 2; }
gridK="8 16 32"; gridW="0.70 0.80 0.90 0.95"
bestS=1e99; bestK=0; bestW=0
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
for K in $gridK; do for W in $gridW; do
  awk -v K="$K" -v W="$W" 'BEGIN{FS="[ \t]+"; OFS="\t"}
    NR==1{prev=$2; tau=$2; t=1; print $1, tau; next}
    { z=$2; for(i=1;i<=K;i++){ tau=W*tau + (1.0-W)*z } ; print $1, tau }
\ "$in" > "$tmp"
  # score: violations + lag-1 corr penalty + var(diff)
  read -r _ < "$tmp" || true
  awk 'BEGIN{OFS="\t"} NR==1{prev=$2; next} {d=$2-prev; prev=$2; diffs[NR-1]=d; if(d< -1e-12) v++ ; s1+=d; s2+=d*d; n++} END{mean=(n?s1/n:0); var=(n? (s2/n - mean*mean):0);
       num=0; den1=0; den2=0; for(i=2;i<=n;i++){ x=diffs[i-1]; y=diffs[i]; num+=x*y; den1+=x*x; den2+=y*y }
       r=(den1>0&&den2>0? num/sqrt(den1*den2):0); score=(1000*v + 100*(r>0?r:0) + (var>0?var:0)); printf "score\t%.9f\tviol\t%d\tr1\t%.6f\n",score,v,r }' "$tmp" > "$tmp.score"
  S=$(awk 'NR==1{print $2}' "$tmp.score")
  if awk -v a="$S" -v b="$bestS" 'BEGIN{exit !(a<b)}'; then bestS="$S"; bestK="$K"; bestW="$W"; fi
done; done
: > "$out"
printf "%s\n" "{" >> "$out"
printf "%s\n" "  \"schema\":\"taucrystal/calibration/v1\"," >> "$out"
printf "%s\n" "  \"tau_class\":\"spectral_or_work\"," >> "$out"
printf "%s\n" "  \"grid\":{\"K\":[8,16,32],\"omega\":[0.70,0.80,0.90,0.95]}," >> "$out"
printf "%s\n" "  \"choice\":{\"K\":$bestK,\"omega\":$bestW,\"score\":$bestS}," >> "$out"
if [ -f ".tau_ledger/operator.json" ]; then
  printf "%s\n" "  \"operator\":$(cat .tau_ledger/operator.json)," >> "$out"
else
  printf "%s\n" "  \"operator\":{\"digest\":\"unknown\",\"size\":0,\"construction\":\"unspecified\"}," >> "$out"
fi
printf "%s\n" "  \"provenance\":{\"run_id\":\"$run_id\",\"host\":\"$(hostname)\",\"ts\":\"$(date -u +%Y-%m-%dT%H:%M:%SZ)\"}" >> "$out"
printf "%s\n" "}" >> "$out"
echo "$out"
