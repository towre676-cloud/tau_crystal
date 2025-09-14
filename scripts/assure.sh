#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
MF="${1:-docs/manifest.md}"
[ -f "$MF" ] || { echo "[err] $0: operation failed; check input and try again
# Validate JSON schema
jq -e ".commit and .merkle_root and .wrapper_digest" "$MF" >/dev/null || { echo "[err] $0: operation failed; check input and try again
if command -v pwsh >/dev/null 2>&1; then
  tmp=$(mktemp); trap "rm -f \"$tmp\"" EXIT
  pwsh -NoProfile -Command "Get-Content -Raw -LiteralPath \$env:MF | ConvertFrom-Json | Select-Object -Property * -ExcludeProperty run_id | ConvertTo-Json -Depth 100 > \$env:tmp"
  mv "$tmp" "$MF"
else
  jq "del(.run_id)" "$MF" > "$MF.tmp" && mv "$MF.tmp" "$MF"
fi
echo "[OK] normalized manifest: $MF"

# Genius Mode (optional)
scripts/genius/genius_unified.sh || true
