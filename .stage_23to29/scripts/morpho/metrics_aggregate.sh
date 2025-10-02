#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage: metrics_aggregate.sh <front_A.tsv> [front_B.tsv] [subject_id] [ipd_px]
A="${1:-}"; B="${2:-}"; SUBJ="${3:-metrics}"; IPD="${4:-}"
[ -n "$A" ] && [ -s "$A" ] || { echo "Provide at least a canonical frontal TSV A (x<TAB>y)."; exit 2; }
TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"; NA="$(basename "${A%.*}")"; NB=""; [ -n "$B" ] && NB="$(basename "${B%.*}")"
OUT="analysis/morpho/${NA}_metrics.tsv"; : > "$OUT"
# Basic span stats on A for width/height.
read -r XMIN XMAX YMIN YMAX COUNT <<< "$(awk -F\"\t\" '{if($1 ~ /^#/)next; if(NF<2)next; x=$1+0; y=$2+0; if(NR==1){xmin=x;xmax=x;ymin=y;ymax=y} else {if(x<xmin)xmin=x; if(x>xmax)xmax=x; if(y<ymin)ymin=y; if(y>ymax)ymax=y}} END{printf(\"%.6f %.6f %.6f %.6f %d\", xmin,xmax,ymin,ymax,NR)}' "$A")"
W=$(awk -v a="$XMIN" -v b="$XMAX" 'BEGIN{printf("%.6f", b-a)}')
H=$(awk -v a="$YMIN" -v b="$YMAX" 'BEGIN{printf("%.6f", b-a)}')
FWHR=$(awk -v w="$W" -v h="$H" 'BEGIN{if(h>0){printf("%.6f", w/h)}else{print "NaN"}}')
# Intra‑file left/right drift on A: mirror x and compare halves (coarse, order‑preserving).
DRIFT=$(awk -F"\t" '{if($1 ~ /^#/ || NF<2)next; x[NR]=$1+0; y[NR]=$2+0} END{n=NR; if(n<2){print "NaN"; exit}; s=0; c=0; for(i=1;i<=n;i++){xm=-x[i]; ym=y[i]; dx=x[i]-xm; dy=y[i]-ym; s+=dx*dx+dy*dy; c++} if(c==0){print "NaN"} else {printf("%.6f", sqrt(s/c))}}' "$A")
RMSAB="NaN"; if [ -n "$B" ] && [ -s "$B" ]; then RMSAB=$(paste "$A" "$B" | awk -F"\t" '{if($1 ~ /^#/ || $3 ~ /^#/)next; if(NF<4)next; dx=$1-$3; dy=$2-$4; s+=dx*dx+dy*dy; n++} END{if(n==0){print "NaN"} else {printf("%.6f", sqrt(s/n))}}'); fi
IPDN=""; if [ -n "$IPD" ]; then IPDN=$(awk -v d="$IPD" -v w="$W" 'BEGIN{if(w>0){printf("%.6f", d/w)}else{print ""}}'); fi
printf "%s\n" "metric\tvalue" >> "$OUT"
printf "%s\t%s\n" "count" "$COUNT" >> "$OUT"
printf "%s\t%s\n" "width" "$W" >> "$OUT"
printf "%s\t%s\n" "height" "$H" >> "$OUT"
printf "%s\t%s\n" "FWHR" "$FWHR" >> "$OUT"
printf "%s\t%s\n" "intraLR_drift" "$DRIFT" >> "$OUT"
printf "%s\t%s\n" "RMS_A_vs_B" "$RMSAB" >> "$OUT"
if [ -n "$IPDN" ]; then printf "%s\t%s\n" "IPD_over_width" "$IPDN" >> "$OUT"; fi
HSH="$(sha256sum "$OUT" | awk "{print \$1}")"; REC=".tau_ledger/morpho/face15/${NA}_metrics_$(printf "%s" "$TS" | tr -cd "0-9").receipt.json"
: > "$REC"
printf "%s" "{" >> "$REC"
printf "%s" "\"kind\":\"morpho/metrics\",\"timestamp\":\"$TS\",\"subject\":\"$SUBJ\",\"sourceA\":\"$A\"" >> "$REC"
if [ -n "$B" ]; then printf "%s" ",\"sourceB\":\"$B\"" >> "$REC"; fi
printf "%s" ",\"sha256\":\"$HSH\"" >> "$REC"
printf "%s\n" "}" >> "$REC"
EV=".tau_ledger/tau_sheaf/events.jsonl"; PRV=""; [ -s "$EV" ] && PRV="$(tail -n 1 "$EV" | sha256sum | awk "{print \$1}")"
RHS="$(sha256sum "$REC" | awk "{print \$1}")"; LID="$(printf "%s" "$TS-$SUBJ-$RHS-FWHR-$FWHR" | sha256sum | awk "{print \$1}")"
J="{\"kind\":\"tau_sheaf/morpho\",\"timestamp\":\"'$TS'\",\"subject\":\"'$SUBJ'\",\"metric\":\"FWHR\",\"value\":'$FWHR',\"receipt_sha256\":\"'$RHS',\"prev\":\"'$PRV',\"lid\":\"'$LID'"}"
printf "%s\n" "$J" >> "$EV"
echo "✅ Aggregated metrics written to $OUT"; echo "Receipt: $REC"
