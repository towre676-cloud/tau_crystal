#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
stem="${1:?usage: save_request_preimage.sh <stem> <file|->}"
src="${2:?usage: save_request_preimage.sh <stem> <file|->}"
out="analysis/${stem}.request.canon.json"
mkdir -p analysis
if [ "$src" = "-" ]; then cat > "$out"; else [ -s "$src" ] || { echo "[err] empty or missing: $src" >&2; exit 2; }; cat "$src" > "$out"; fi
if command -v sha256sum >/dev/null 2>&1; then h=$(sha256sum "$out" | awk "{print \\$1}"); else h=$(openssl dgst -sha256 "$out" | awk "{print \\$2}"); fi
printf "%s\n" "$h"
