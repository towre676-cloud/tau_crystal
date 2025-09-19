#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage: face15_ingest.sh <FACE.txt> [subject_id]
IN="${1:-}"; SUBJ="${2:-face15}"
[ -n "$IN" ] && [ -s "$IN" ] || { echo "Provide FACE.txt with 15 key: value lines."; exit 2; }
H="$(sha256sum "$IN" 2>/dev/null | awk "{print \$1}")"; TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
B="$(basename "$IN")"; N="${B%.*}"; REC=".tau_ledger/morpho/face15/${N}_$(printf "%s" "$TS" | tr -cd "0-9").receipt.json"
TMP=".tau_ledger/morpho/face15/${N}.tmp.tsv"; : > "$TMP"
# Extract first 15 numeric key:value pairs (case‑insensitive, spaces tolerated).
awk -F: '{k=$1; v=$2; gsub(/[ \t\r\n]+/,"",k); gsub(/[ \t\r\n]+/,"",v); if(k!="" && v ~ /^-?[0-9.]+$/){print k"\t"v}}' "$IN" | head -n 15 > "$TMP"
CNT=$(wc -l < "$TMP" | tr -d " ")
[ "$CNT" -ge 1 ] || { echo "[face15] no numeric fields found"; exit 3; }
# Compute simple summary stats over the 15 values to offer an extra analytic signal.
SUM=$(awk -F"\t" '{s+=$2} END{printf("%.8f", s+0)}' "$TMP")
MEAN=$(awk -F"\t" -v c="$CNT" '{s+=$2} END{if(c>0){printf("%.8f", s/c)}else{print "NaN"}}' "$TMP")
STD=$(awk -F"\t" -v c="$CNT" -v m="" '{d=$2-m; s+=d*d} END{if(c>1){printf("%.8f", sqrt(s/(c-1)))}else{print "NaN"}}' "$TMP")
# HarmonyIndex is a dimensionless 0..1 heuristic: 1 / (1 + STD). Lower STD → closer to 1.
HIX=$(awk -v s="$STD" 'BEGIN{if(s ~ /^[0-9.]+$/){printf("%.6f", 1/(1+s))}else{print "NaN"}}')
: > "$REC"
printf "%s" "{" >> "$REC"
printf "%s" "\"kind\":\"morpho/face15\",\"timestamp\":\"$TS\",\"subject\":\"$SUBJ\",\"source\":\"$IN\",\"sha256\":\"$H\"," >> "$REC"
printf "%s" "\"count\":$CNT,\"mean\":$MEAN,\"std\":$STD,\"harmonyIndex\":$HIX,\"kvs\":[" >> "$REC"
i=0; while IFS=$'\t' read -r K V; do i=$((i+1)); escK=$(printf "%s" "$K" | sed "s/\"/\\"/g"); printf "%s" "{\"k\":\"$escK\",\"v\":$V}" >> "$REC"; if [ "$i" -lt "$CNT" ]; then printf "%s" "," >> "$REC"; fi; done < "$TMP"
printf "%s\n" "]}" >> "$REC"
EV=".tau_ledger/tau_sheaf/events.jsonl"; TSV="analysis/morpho/face15.tsv"; RHS="$(sha256sum "$REC" | awk "{print \$1}")"
PRV=""; [ -s "$EV" ] && PRV="$(tail -n 1 "$EV" | sha256sum | awk "{print \$1}")"
LID="$(printf "%s" "$TS-$SUBJ-$RHS-face15-$HIX" | sha256sum | awk "{print \$1}")"
mkdir -p "$(dirname "$EV")" "$(dirname "$TSV")"
J="{\"kind\":\"tau_sheaf/morpho\",\"timestamp\":\"'$TS'\",\"subject\":\"'$SUBJ'\",\"metric\":\"face15_harmony\",\"value\":'$HIX',\"receipt_sha256\":\"'$RHS',\"prev\":\"'$PRV',\"lid\":\"'$LID'"}"
printf "%s\n" "$J" >> "$EV"
if [ ! -s "$TSV" ]; then printf "%s\n" "timestamp\tsubject\tcount\tmean\tstd\tharmonyIndex\treceipt_sha256\tlid" > "$TSV"; fi
printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$TS" "$SUBJ" "$CNT" "$MEAN" "$STD" "$HIX" "$RHS" "$LID" >> "$TSV"
rm -f "$TMP"; echo "✅ FACE15 ingested: mean=$MEAN std=$STD harmonyIndex=$HIX"; echo "Receipt: $REC"
