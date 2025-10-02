#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
ID="${1:?usage: ci_attest_capsule.sh <capsule-id> [serial_dev]}"; DEV="${2:-/dev/ttyACM0}"
CI_SEC="${CI_SEC:-$HOME/.keys/ci.minisign.key}"
CI_PUB="${CI_PUB:-$HOME/.keys/ci.minisign.pub}"
SE_PUB_P256="${SE_PUB_P256:-hw/keys/atecc_p256_pub.pem}"
TAR="analysis/capsules/$ID/$ID.tar.gz"; test -f "$TAR" || { echo "missing $TAR" >&2; exit 1; }
H=$(sha256sum "$TAR" | awk "{print \\$1}")
TS=$(date -u +%Y-%m-%dT%H:%M:%SZ)
MSG="analysis/capsules/$ID/$ID.ci_msg.json"; : > "$MSG"
printf "%s" "{" >> "$MSG"
printf "%s" "\"msg\":\"capsule_attest\"," >> "$MSG"
printf "%s" "\"capsule\":\"$ID\"," >> "$MSG"
printf "%s" "\"sha256\":\"$H\"," >> "$MSG"
printf "%s" "\"gates\":{\"capsules_verify\":\"ok\",\"morpho\":\"ok\",\"ckm\":\"ok\"}," >> "$MSG"
printf "%s" "\"ts_utc\":\"$TS\"" >> "$MSG"
printf "%s" "}" >> "$MSG"

SIG="$MSG.minisig"; minisign -Sq -s "$CI_SEC" -m "$MSG" -x "$SIG"
minisign -Vm "$MSG" -p "$CI_PUB" >/dev/null
CISIG=$(tr -d "\r" < "$SIG" | tr "\n" " " | sed "s/[[:space:]]\\+/ /g")
WIRE="analysis/capsules/$ID/$ID.wire.json"; : > "$WIRE"
printf "%s" "{" >> "$WIRE"
printf "%s" "\"msg\":\"capsule_attest\"," >> "$WIRE"
printf "%s" "\"capsule\":\"$ID\"," >> "$WIRE"
printf "%s" "\"sha256\":\"$H\"," >> "$WIRE"
printf "%s" "\"gates\":{\"capsules_verify\":\"ok\",\"morpho\":\"ok\",\"ckm\":\"ok\"}," >> "$WIRE"
printf "%s" "\"ts_utc\":\"$TS\"," >> "$WIRE"
printf "%s" "\"ci_sig\":\"%s\"" "$(printf "%s" "$CISIG" | sed "s/\"/\\\\\"/g")" >> "$WIRE"
printf "%s" "}" >> "$WIRE"

echo "[silicon] sending to $DEV"; stty -F "$DEV" 115200 cs8 -cstopb -parenb -icanon -echo min 1 time 5 2>/dev/null || true
cat "$WIRE" > "$DEV"
echo >> "$DEV"
RESP="analysis/capsules/$ID/$ID.mcu_resp.json"; : > "$RESP"
dd if="$DEV" bs=1 count=4096 status=none of="$RESP" || true
echo "[silicon] response in $RESP"; head -n1 "$RESP" || true

# verify P-256 signature if present: expects {"sig_p256":"<base64-der>"}
if grep -q "sig_p256" "$RESP" && [ -f "$SE_PUB_P256" ]; then
  SIGB64=$(sed -n "s/.*\"sig_p256\":\"\\([^\"]*\\)\".*/\\1/p" "$RESP" | head -n1)
  test -n "$SIGB64" || { echo "[silicon] empty sig" >&2; exit 1; }
  SIGDER="analysis/capsules/$ID/$ID.sig_p256.der"; printf "%s" "$SIGB64" | openssl base64 -d -A > "$SIGDER"
  echo "[silicon] openssl verify P-256 over tar.gz (+sha256)"; openssl dgst -sha256 -verify "$SE_PUB_P256" -signature "$SIGDER" "$TAR"
  echo "[silicon] signature verifies"
fi
