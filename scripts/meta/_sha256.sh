#!/usr/bin/env bash
# lines: 15
set -Eeuo pipefail; set +H; umask 022
f="${1:-}"; [ -n "$f" ] && [ -f "$f" ] || { echo "usage: $0 <file>" >&2; exit 2; }
if command -v sha256sum >/dev/null 2>&1; then
  sha256sum "$f" | cut -d" " -f1; exit 0
fi
if command -v shasum >/dev/null 2>&1; then
  shasum -a 256 "$f" | cut -d" " -f1; exit 0
fi
openssl dgst -sha256 "$f" 2>/dev/null | awk '{print $2}' && exit 0
# last-resort pure POSIX (slow): xxd not guaranteed; so fail clearly
echo "[ERR] no sha tool available" >&2; exit 3
