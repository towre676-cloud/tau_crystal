#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage: zk_diff_chain.sh <norm_landmarks_A.tsv> <norm_landmarks_B.tsv> [threshold]
A="${1:-}"; B="${2:-}"; TH="${3:-0.0100}"
[ -n "$A" ] && [ -s "$A" ] && [ -n "$B" ] && [ -s "$B" ] || { echo "[zk_diff] missing inputs"; exit 2; }
HA="$(sha256sum "$A" 2>/dev/null | awk "{print \$1}")"; HB="$(sha256sum "$B" 2>/dev/null | awk "{print \$1}")"
[ -n "$HA" ] && [ -n "$HB" ] || { echo "[zk_diff] sha256sum unavailable"; exit 3; }
TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
NA="$(basename "${A%.*}")"; NB="$(basename "${B%.*}")"
REC=".tau_ledger/morpho/zk/${NA}__${NB}_$(printf "%s" "$TS" | tr -cd "0-9").receipt.json"
# Count lines (non-empty, not starting with #). Ensure same length.
LA=$(grep -Evc "^\s*(#|$)" "$A"); LB=$(grep -Evc "^\s*(#|$)" "$B")
if [ "$LA" -ne "$LB" ]; then echo "[zk_diff] landmark count mismatch: $LA vs $LB"; exit 4; fi
# Compute RMS over first two numeric columns in each file.
RMS=$(paste "$A" "$B" | awk -F"\t" '{if($1 ~ /^#/ || $3 ~ /^#/ )next; if(NF<4)next; x1=$1+0; y1=$2+0; x2=$3+0; y2=$4+0; dx=x1-x2; dy=y1-y2; s+=dx*dx+dy*dy; n++} END{ if(n==0){print "NaN"} else {printf("%.6f", sqrt(s/n))} }')
case "$RMS" in *[!0-9.]*|"") echo "[zk_diff] invalid RMS"; exit 5;; esac
ok=$(awk -v r="$RMS" -v t="$TH" 'BEGIN{print (r<=t)?1:0}')
# Salted commitments to hide raw hashes in public receipts.
SALT="$(printf "%s" "$(hostname)-$$-$(date +%s)-$RANDOM" | sha256sum | awk "{print \$1}")"
CA="$(printf "%s%s" "$HA" "$SALT" | sha256sum | awk "{print \$1}")"
CB="$(printf "%s%s" "$HB" "$SALT" | sha256sum | awk "{print \$1}")"
: > "$REC"
printf "%s" "{" >> "$REC"
printf "%s" "\"kind\":\"morpho/zk_diff\",\"timestamp\":\"$TS\"," >> "$REC"
printf "%s" "\"a_commit\":\"$CA\",\"b_commit\":\"$CB\",\"salt_sha256\":\"$SALT\"," >> "$REC"
printf "%s" "\"metric\":\"RMS\",\"value\":$RMS,\"threshold\":$TH,\"accept\":$ok" >> "$REC"
printf "%s\n" "}" >> "$REC"
echo "[zk_diff] RMS=$RMS threshold=$TH accept=$ok"
echo "[zk_diff] wrote $REC"
