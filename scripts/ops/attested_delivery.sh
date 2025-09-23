#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022

ID="${1:-auto-$(date -u +%Y%m%dT%H%M%SZ)}"
PAID_METHOD="${PAID_METHOD:-stripe}"
AMOUNT_USD="${AMOUNT_USD:-0}"
PAID_AT_UTC="${PAID_AT_UTC:-$(date -u +%Y-%m-%dT%H:%M:%SZ)}"
PAYMENT_REF="${PAYMENT_REF:-unknown}"
MINISIGN_SEC="${MINISIGN_SEC:-$HOME/.keys/minisign.key}"
MINISIGN_PUB="${MINISIGN_PUB:-$HOME/.keys/minisign.pub}"

OUT="analysis/capsules/$ID"; mkdir -p "$OUT"
TAR="$OUT/$ID.tar.gz"
SHA="$OUT/$ID.tar.gz.sha256"
REC="$OUT/$ID.receipt.json"
LEDGER_DIR=".tau_ledger/delivery/$(date -u +%Y)/$(date -u +%m)"; mkdir -p "$LEDGER_DIR"
LEDGER="$LEDGER_DIR/$ID.json"

echo "[attested_delivery] packaging capsule $ID"
tar -czf "$TAR" analysis progress docs || true
SIZE=$(wc -c < "$TAR" | tr -d " ")
sha256sum "$TAR" | awk "{print \\$1}" > "$SHA"
H=$(cat "$SHA")

echo "[attested_delivery] minisign seller signature"
test -f "$MINISIGN_SEC" || { echo "Missing MINISIGN key: $MINISIGN_SEC" >&2; exit 1; }
minisign -Sq -s "$MINISIGN_SEC" -m "$TAR" -x "$TAR.minisig"
SELLER_SIG=$(tr -d "\r" < "$TAR.minisig" | tr "\n" " " | sed "s/[[:space:]]\\+/ /g")

echo "[attested_delivery] emitting receipt json"
: > "$REC"
printf "%s" "{" >> "$REC"
printf "%s" "\"type\":\"attested_delivery\"," >> "$REC"
printf "%s" "\"capsule\":\"$ID\"," >> "$REC"
printf "%s" "\"sha256\":\"$H\"," >> "$REC"
printf "%s" "\"size_bytes\":$SIZE," >> "$REC"
printf "%s" "\"seller_sig\":\"%s\"," "$(printf "%s" "$SELLER_SIG" | sed "s/\"/\\\\\"/g")" >> "$REC"
printf "%s" "\"paid\":{" >> "$REC"
printf "%s" "\"method\":\"$PAID_METHOD\"," >> "$REC"
printf "%s" "\"amount_usd\":$AMOUNT_USD," >> "$REC"
printf "%s" "\"paid_at_utc\":\"$PAID_AT_UTC\"," >> "$REC"
printf "%s" "\"payment_ref\":\"$PAYMENT_REF\"" >> "$REC"
printf "%s" "}" >> "$REC"
printf "%s" "}" >> "$REC"

echo "[attested_delivery] ledger write"
: > "$LEDGER"
printf "%s\n" "{" >> "$LEDGER"
printf "%s\n" "  \"capsule\":\"$ID\"," >> "$LEDGER"
printf "%s\n" "  \"sha256\":\"$H\"," >> "$LEDGER"
printf "%s\n" "  \"size_bytes\":$SIZE," >> "$LEDGER"
printf "%s\n" "  \"tar\":\"$TAR\"," >> "$LEDGER"
printf "%s\n" "  \"sha256_file\":\"$SHA\"," >> "$LEDGER"
printf "%s\n" "  \"receipt\":\"$REC\"," >> "$LEDGER"
printf "%s\n" "  \"seller_sig_file\":\"$TAR.minisig\"," >> "$LEDGER"
printf "%s\n" "  \"paid\":{\"method\":\"$PAID_METHOD\",\"amount_usd\":$AMOUNT_USD,\"paid_at_utc\":\"$PAID_AT_UTC\",\"payment_ref\":\"$PAYMENT_REF\"}" >> "$LEDGER"
printf "%s\n" "}" >> "$LEDGER"

echo "[attested_delivery] self-verify"
H2=$(sha256sum "$TAR" | awk "{print \\$1}")
[ "$H" = "$H2" ] || { echo "sha mismatch" >&2; exit 1; }
minisign -Vm "$TAR" -p "$MINISIGN_PUB" >/dev/null
echo "[attested_delivery] ready: $TAR  $SHA  $REC"
