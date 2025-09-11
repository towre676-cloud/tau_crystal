#!/usr/bin/env bash
set -euo pipefail; set +H
f="${1:?json file}"
if command -v jq >/dev/null 2>&1; then canon="$(jq -S -c . "$f")"; else canon="$(python3 scripts/bin/json_c14n.py "$f")"; fi
if command -v sha256sum >/dev/null 2>&1; then printf "%s" "$canon" | sha256sum | awk "{print \$1}"; else printf "%s" "$canon" | openssl dgst -sha256 | awk "{print \$2}"; fi
