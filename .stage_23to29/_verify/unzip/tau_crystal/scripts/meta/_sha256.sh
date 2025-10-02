#!/usr/bin/env bash
set -o pipefail
[ -n "$1" ] || { echo "usage: _sha256.sh <path>" >&2; exit 2; }
if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'; exit; fi
if command -v shasum    >/dev/null 2>&1; then shasum -a 256 "$1" | awk '{print $1}'; exit; fi
openssl dgst -sha256 "$1" 2>/dev/null | awk '{print $NF}'
