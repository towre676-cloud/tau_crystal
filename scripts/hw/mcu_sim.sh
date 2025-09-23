#!/usr/bin/env bash
set -e; set +H; umask 022
PRIV="hw/keys/device_p256.key"
read -r LINE || { echo "{\"msg\":\"denied\",\"reason\":\"no_input\"}"; exit 0; }
CAP=$(printf "%s" "$LINE" | sed -n "s/.*\"capsule\":\"\\([^\"]*\\)\".*/\\1/p")
H=$(printf "%s" "$LINE" | sed -n "s/.*\"sha256\":\"\\([^\"]*\\)\".*/\\1/p")
G1=$(printf "%s" "$LINE" | sed -n "s/.*\"capsules_verify\":\"\\([^\"]*\\)\".*/\\1/p")
G2=$(printf "%s" "$LINE" | sed -n "s/.*\"morpho\":\"\\([^\"]*\\)\".*/\\1/p")
G3=$(printf "%s" "$LINE" | sed -n "s/.*\"ckm\":\"\\([^\"]*\\)\".*/\\1/p")
[ "$CAP" ] && [ "$H" ] || { echo "{\"msg\":\"denied\",\"reason\":\"bad_fields\"}"; exit 0; }
[ "$G1" = "ok" ] && [ "$G2" = "ok" ] && [ "$G3" = "ok" ] || { echo "{\"msg\":\"denied\",\"reason\":\"policy_mismatch\"}"; exit 0; }
TAR="analysis/capsules/$CAP/$CAP.tar.gz"; [ -f "$TAR" ] || { echo "{\"msg\":\"denied\",\"reason\":\"missing_tar\"}"; exit 0; }
H2=$(sha256sum "$TAR" | cut -d" " -f1)
[ "$H" = "$H2" ] || { echo "{\"msg\":\"denied\",\"reason\":\"hash_mismatch\"}"; exit 0; }
SIGDER="$(mktemp)"; openssl dgst -sha256 -sign "$PRIV" -out "$SIGDER" "$TAR"
SIGB64=$(openssl base64 -A -in "$SIGDER")
printf "{\"msg\":\"capsule_signed\",\"capsule\":\"%s\",\"sig_p256\":\"%s\"}\n" "$CAP" "$SIGB64"
