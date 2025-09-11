#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
IN="${1:-}"; OUT="${2:-}"
[ -n "$IN" ] && [ -n "$OUT" ] && [ -f "$IN" ] || {
  printf "{\"ok\":false,\"error\":\"usage: physics_verifier.sh <in.json> <out.json>\"}\n" > "${OUT:-/dev/stdout}"; exit 2;
}
TMP="$(mktemp)"; trap 'rm -f "$TMP"' EXIT
if command -v python3 >/dev/null 2>&1; then
  python3 scripts/tools/physics_verifier.py "$IN" > "$TMP" 2>/dev/null || {
    printf "{\"ok\":false,\"error\":\"python_failed\"}\n" > "$TMP";
  }
else
  printf "{\"ok\":false,\"error\":\"python3_not_found\"}\n" > "$TMP"
fi
mv -f "$TMP" "$OUT"
