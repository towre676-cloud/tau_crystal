#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
msg=$(git log -1 --pretty=%B 2>/dev/null | tr -d "\r")
file=$(printf "%s\n" "$msg" | awk -F"Testimony:" '{if(NF>1){gsub(/^[ \t]+/,"",$2);print $2}}')
if [ -z "${file:-}" ]; then echo "[testimony] no Testimony: tag in HEAD message; pass (noop)"; exit 0; fi
path="docs/testimony/$file"
[ -s "$path" ] || { echo "[testimony] missing or empty: $path"; exit 2; }
head -n 1 "$path" | grep -qE "^[#=]|^Title:" || { echo "[testimony] first line lacks a title marker: $path"; exit 3; }
bytes=$(wc -c < "$path" | tr -d " \r\n")
[ "${bytes:-0}" -ge 200 ] || { echo "[testimony] too short (<200 bytes): $path"; exit 4; }
sha=$(openssl dgst -sha256 "$path" | awk "{print \$NF}")
commit=$(git rev-parse HEAD)
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
out=".tau_ledger/testimony/${commit}.attest"
: > "$out"
printf "%s\n" "{ \"commit\": \"${commit}\", \"testimony\": \"${file}\", \"sha256\": \"${sha}\", \"utc\": \"${ts}\" }" >> "$out"
echo "[testimony] ok: $file (#$bytes bytes, sha=$sha) → $out"
