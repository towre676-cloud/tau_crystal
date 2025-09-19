#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
ROOT=".tau_ledger"; CHAIN="$ROOT/CHAIN"; TMP="$ROOT/.tmp.sheaf"; PRE="$ROOT/sheaf.preimage"; OUT="$ROOT/sheaf.digest"
[ -s "$CHAIN" ] || : > "$CHAIN"
rm -f "$TMP" "$PRE" "$OUT"
scripts/meta/_normalize.sh "$CHAIN" "$TMP"
LC=$(wc -l < "$TMP" | tr -d " ")
STAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
printf "%s\n" "tau_sheaf_v1" > "$PRE"
printf "%s\n" "lines:$LC" >> "$PRE"
printf "%s\n" "stamp:$STAMP" >> "$PRE"
ROLL=""; i=0
while IFS= read -r h; do i=$((i+1)); ROLL=$(printf "%s" "$ROLL$h" | openssl dgst -sha256 | awk "{print \$2}"); printf "%s\n" "[$i] $ROLL" >> "$PRE"; done < "$TMP"
DIGEST=$(scripts/meta/_sha256.sh "$PRE")
printf "%s" "$DIGEST" > "$OUT"
printf "%s\n" "[sheaf] $DIGEST" >> "$CHAIN"
echo "$DIGEST"
