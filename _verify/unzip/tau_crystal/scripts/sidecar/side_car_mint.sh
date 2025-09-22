#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
PAY="${1:-}"; OUT="${2:-}"; PROD="${3:-${USER:-unknown}}"; SRC="${4:-local}"; MIME="${5:-application/octet-stream}"
[ -n "$PAY" ] && [ -f "$PAY" ] || { echo "[mint] need payload file" >&2; exit 2; }
[ -n "$OUT" ] || { echo "[mint] need output pack name" >&2; exit 2; }
tmp=$(mktemp -d); trap "rm -rf \"$tmp\"" EXIT
cp -f "$PAY" "$tmp/payload.bin"
BYTES=$(wc -c < "$tmp/payload.bin" | tr -d " ")
if command -v sha256sum >/dev/null 2>&1; then H=$(sha256sum "$tmp/payload.bin" | cut -d" " -f1); else H=$(shasum -a 256 "$tmp/payload.bin" | cut -d" " -f1); fi
: > "$tmp/side_car.json"
printf "%s\n" "{" >> "$tmp/side_car.json"
printf "%s\n" "  \"schema\": \"side-car-v1\"," >> "$tmp/side_car.json"
printf "%s\n" "  \"version\": 1," >> "$tmp/side_car.json"
printf "%s\n" "  \"payload_sha256\": \"$H\"," >> "$tmp/side_car.json"
printf "%s\n" "  \"payload_bytes\": $BYTES," >> "$tmp/side_car.json"
printf "%s\n" "  \"payload_mime\": \"$MIME\"," >> "$tmp/side_car.json"
printf "%s\n" "  \"meta\": {\"source\":\"$SRC\",\"producer\":\"$PROD\",\"ts\":\"$(date -u +"%Y-%m-%dT%H:%M:%SZ")\"}" >> "$tmp/side_car.json"
printf "%s\n" "}" >> "$tmp/side_car.json"
( cd "$tmp" && tar -czf "$OLDPWD/$OUT" side_car.json payload.bin )
echo "[mint] wrote $OUT ($BYTES bytes, sha256=$H)"
