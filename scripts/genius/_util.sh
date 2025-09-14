#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
sha(){
  if [ "${1:-}" = "-" ]; then
    if command -v sha256sum >/dev/null 2>&1; then sha256sum - | awk "{print \$1}"; else openssl dgst -sha256 -stdin | awk "{print \$2}"; fi
  else
    if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk "{print \$1}"; else openssl dgst -sha256 "$1" | awk "{print \$2}"; fi
  fi
}
ts(){ date -u +%Y%m%dT%H%M%SZ; }
emit_kv(){ printf "%s\n" "$1: $2" >> "$3"; }
selfhash(){ sha "$1"; }
