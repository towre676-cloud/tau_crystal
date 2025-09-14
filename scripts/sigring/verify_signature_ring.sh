#!/usr/bin/env bash
set -Eeuo pipefail; set +H
dir=".tau_ledger/sigring"; j=$(ls -1 "$dir"/ringv1-*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -n "$j" ] || { echo "::error ::no ring json"; exit 1; }
pub="$(awk '/BEGIN PUBLIC KEY/{f=1} f{print} /END PUBLIC KEY/{f=0}' "$j" | sed -n "1,200p")"
sigb64=$(grep -m1 -o "\"signature_b64\": *\"[^\"]\\+\"" "$j" | sed "s/.*: *\"\([^\"]\+\)\".*/\1/")
tmp="$(mktemp)"; trap "rm -f \"$tmp\"" EXIT
awk '/^[[:space:]]*"lines"[[:space:]]*:[[:space:]]*\[/{f=1; next} f&&/\]/{f=0} f{gsub(/^[[:space:]]*\"|\",?$/,""); print}' "$j" | sed "/^$/d" > "$tmp"
printf "%s\n" "$pub" > "$dir/.pub.pem"
printf "%s" "$sigb64" | openssl base64 -d -A > "$dir/.sig.bin"
if openssl pkeyutl -verify -pubin -inkey "$dir/.pub.pem" -rawin -in "$tmp" -sigfile "$dir/.sig.bin" >/dev/null 2>&1; then echo "OK: signature ring verified"; else echo "FAIL: signature ring verify failed"; exit 1; fi
