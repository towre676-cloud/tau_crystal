#!/usr/bin/env bash
set -e; set +H; umask 022
ID="${1:?usage: ci_attest_capsule_p256.sh <capsule-id> <dev|SIM>}"; DEV="${2:-SIM}"
PUB="${DEVICE_PUB:-hw/keys/device_p256.pub.pem}"
TAR="analysis/capsules/$ID/$ID.tar.gz"; [ -f "$TAR" ] || { echo "missing $TAR" >&2; exit 1; }
H=$(sha256sum "$TAR" | cut -d" " -f1)
TS=$(date -u +%Y-%m-%dT%H:%M:%SZ)
WIRE=$(mktemp); : > "$WIRE"
printf "%s" "{" >> "$WIRE"
printf "%s" "\"msg\":\"capsule_attest\"," >> "$WIRE"
printf "%s" "\"capsule\":\"$ID\"," >> "$WIRE"
printf "%s" "\"sha256\":\"$H\"," >> "$WIRE"
printf "%s" "\"gates\":{\"capsules_verify\":\"ok\",\"morpho\":\"ok\",\"ckm\":\"ok\"}," >> "$WIRE"
printf "%s" "\"ts_utc\":\"$TS\"" >> "$WIRE"
printf "%s" "}" >> "$WIRE"
printf "\n" >> "$WIRE"  # ensure newline for read -r
RESP=$(mktemp)
if [ "$DEV" = "SIM" ]; then
  cat "$WIRE" | scripts/hw/mcu_sim.sh > "$RESP"
else
  stty -F "$DEV" 115200 cs8 -cstopb -parenb -icanon -echo min 1 time 5 2>/dev/null || true
  cat "$WIRE" > "$DEV"; echo >> "$DEV"
  dd if="$DEV" bs=1 count=4096 status=none of="$RESP" || true
fi
echo "[silicon] device response:"
head -n1 "$RESP"
SIGB64=$(sed -n "s/.*\"sig_p256\":\"\\([^\"]*\\)\".*/\\1/p" "$RESP" | head -n1)
[ -n "$SIGB64" ] || { echo "[silicon] denied or no signature"; cat "$RESP"; exit 1; }
SIGDER=$(mktemp); printf "%s" "$SIGB64" | openssl base64 -d -A > "$SIGDER"
echo "[silicon] verifying P-256 signature with $PUB"
openssl dgst -sha256 -verify "$PUB" -signature "$SIGDER" "$TAR"
echo "[silicon] verified OK"
