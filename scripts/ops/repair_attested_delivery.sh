#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
ID="${1:?usage: repair_attested_delivery.sh <capsule-id> [amount_usd] [method] [paid_at_utc] [payment_ref] }"
AMOUNT="${2:-0}"
METHOD="${3:-stripe}"
PAID_AT="${4:-$(date -u +%Y-%m-%dT%H:%M:%SZ)}"
PAYREF="${5:-unknown}"
SEC="${MINISIGN_SEC:-$HOME/.keys/minisign.key}"
PUB="${MINISIGN_PUB:-$HOME/.keys/minisign.pub}"
OUT="analysis/capsules/$ID"
TAR="$OUT/$ID.tar.gz"; SHAF="$OUT/$ID.tar.gz.sha256"; REC="$OUT/$ID.receipt.json"
[ -f "$TAR" ] || { echo "[repair] missing $TAR — run packaging first." >&2; exit 1; }
hash_tar(){
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | tr -d "\r" | cut -d" " -f1; return; fi
  if command -v certutil   >/dev/null 2>&1; then certutil -hashfile "$(cygpath -w "$1" 2>/dev/null || echo "$1")" SHA256 2>/dev/null | sed -n "2p" | tr -d " \r\n"; return; fi
  echo "[repair] need sha256sum or certutil" >&2; exit 1
}

mkdir -p "$OUT" "$HOME/.keys"
[ -f "$SEC" ] && [ -f "$PUB" ] || { echo "[repair] generating minisign keypair under $HOME/.keys"; minisign -G -s "$SEC" -p "$PUB" -q; }
echo "[repair] recompute sha256 → $SHAF"
H=$(hash_tar "$TAR")
: > "$SHAF"; printf "%s\n" "$H" >> "$SHAF"
SIZE=$(wc -c < "$TAR" | tr -d " ")

echo "[repair] minisign tar → $TAR.minisig"
minisign -Sq -s "$SEC" -m "$TAR" -x "$TAR.minisig"

echo "[repair] emit receipt → $REC"
: > "$REC"
printf "%s" "{" >> "$REC"
printf "%s" "\"type\":\"attested_delivery\"," >> "$REC"
printf "%s" "\"capsule\":\"$ID\"," >> "$REC"
printf "%s" "\"sha256\":\"$H\"," >> "$REC"
printf "%s" "\"size_bytes\":$SIZE," >> "$REC"
SIGTXT=$(tr -d "\r" < "$TAR.minisig" | tr "\n" " " | sed "s/[[:space:]]\\+/ /g")
printf "%s" "\"seller_sig\":\"%s\"," "$(printf "%s" "$SIGTXT" | sed "s/\"/\\\\\"/g")" >> "$REC"
printf "%s" "\"paid\":{" >> "$REC"
printf "%s" "\"method\":\"$METHOD\"," >> "$REC"
printf "%s" "\"amount_usd\":$AMOUNT," >> "$REC"
printf "%s" "\"paid_at_utc\":\"$PAID_AT\"," >> "$REC"
printf "%s" "\"payment_ref\":\"$PAYREF\"" >> "$REC"
printf "%s" "}" >> "$REC"
printf "%s" "}" >> "$REC"

echo "[repair] verify minisign"
minisign -Vm "$TAR" -p "$PUB" >/dev/null
echo "[repair] pubkey line for README: "
printf "Seller public key (minisign): "; tr -d "\r\n" < "$PUB"; echo
echo "[repair] done: $TAR  $SHAF  $REC  $TAR.minisig"
