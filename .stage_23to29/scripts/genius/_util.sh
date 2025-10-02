#!/usr/bin/env bash
set -Eeuo pipefail; set +H
ts(){ date -u +%Y%m%dT%H%M%SZ; }
sha(){
  if [ "${1:-}" = "-" ]; then
    if command -v sha256sum >/dev/null 2>&1; then sha256sum - | awk '{print $1}'; else openssl dgst -sha256 -r | awk '{print $1}'; fi
  else
    if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'; else openssl dgst -sha256 "$1" | awk '{print $2}'; fi
  fi
}
emit_kv(){ printf '%s: %s\n' "$1" "$2" >> "$3"; }
pi(){ awk 'BEGIN{print atan2(0,-1)}'; }
sin2(){ awk -v a="$1" 'BEGIN{print (sin(a))^2}'; }
