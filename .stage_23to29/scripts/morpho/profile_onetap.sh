#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage: profile_onetap.sh <left.tsv> <right.tsv> [subject_id] [threshold]
L="${1:-}"; R="${2:-}"; SUBJ="${3:-profile}"; TH="${4:-0.0100}"
[ -n "$L" ] && [ -s "$L" ] && [ -n "$R" ] && [ -s "$R" ] || { echo "Provide left.tsv and right.tsv (x<TAB>y per row)."; exit 2; }
TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
NA="$(basename "${L%.*}")"; NB="$(basename "${R%.*}")"
REC=".tau_ledger/morpho/profile/${NA}__${NB}_$(printf "%s" "$TS" | tr -cd "0-9").receipt.json"
LA=$(grep -Evc "^[[:space:]]*(#|$)" "$L"); RB=$(grep -Evc "^[[:space:]]*(#|$)" "$R")
if [ "$LA" -ne "$RB" ]; then echo "[profile] landmark mismatch: $LA vs $RB"; exit 4; fi
RMS=$(paste "$L" "$R" | awk -F"\t" '{if($1 ~ /^#/ || $3 ~ /^#/)next; if(NF<4)next; xL=$1+0; yL=$2+0; xR=-($3+0); yR=$4+0; dx=xL-xR; dy=yL-yR; s+=dx*dx+dy*dy; n++} END{ if(n==0){print "NaN"} else {printf("%.6f", sqrt(s/n))} }')
case "$RMS" in *[!0-9.]*|"") echo "[profile] invalid RMS"; exit 5;; esac
ACC=$(awk -v r="$RMS" -v t="$TH" 'BEGIN{print (r<=t)?1:0}')
HL="$(sha256sum "$L" 2>/dev/null | awk "{print \$1}")"; HR="$(sha256sum "$R" 2>/dev/null | awk "{print \$1}")"
SALT="$(printf "%s" "$(hostname)-$$-$(date +%s)-$RANDOM" | sha256sum | awk "{print \$1}")"
CL="$(printf "%s%s" "$HL" "$SALT" | sha256sum | awk "{print \$1}")"; CR="$(printf "%s%s" "$HR" "$SALT" | sha256sum | awk "{print \$1}")"
: > "$REC"
printf "%s" "{" >> "$REC"
printf "%s" "\"kind\":\"morpho/profile_sym\",\"timestamp\":\"$TS\"," >> "$REC"
printf "%s" "\"left_commit\":\"$CL\",\"right_commit\":\"$CR\",\"salt_sha256\":\"$SALT\"," >> "$REC"
printf "%s" "\"metric\":\"RMS\",\"value\":$RMS,\"threshold\":$TH,\"accept\":$ACC" >> "$REC"
printf "%s\n" "}" >> "$REC"
VAL="$RMS"; RHS="$(sha256sum "$REC" | awk "{print \$1}")"
EV=".tau_ledger/tau_sheaf/events.jsonl"; TSV="analysis/morpho/tau_profile.tsv"
PRV=""; [ -s "$EV" ] && PRV="$(tail -n 1 "$EV" | sha256sum | awk "{print \$1}")"
LID="$(printf "%s" "$TS-$SUBJ-$RHS-profileRMS-$VAL" | sha256sum | awk "{print \$1}")"
mkdir -p "$(dirname "$EV")" "$(dirname "$TSV")"
J="{\"kind\":\"tau_sheaf/morpho\",\"timestamp\":\"$TS\",\"subject\":\"$SUBJ\",\"metric\":\"profile_RMS\",\"value\":$VAL,\"receipt_sha256\":\"$RHS\",\"prev\":\"$PRV\",\"lid\":\"$LID\"}"
printf "%s\n" "$J" >> "$EV"
if [ ! -s "$TSV" ]; then printf "%s\n" "timestamp\tsubject\tmetric\tvalue\treceipt_sha256\tprev\tlid" > "$TSV"; fi
printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$TS" "$SUBJ" "profile_RMS" "$VAL" "$RHS" "$PRV" "$LID" >> "$TSV"
echo "OK profile: RMS=$RMS accept=$ACC"; echo "Receipt: $REC"
