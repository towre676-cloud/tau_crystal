#!/usr/bin/env bash
set -euo pipefail
MAN="docs/manifest.md"
[ -f "$MAN" ] || printf '# τ‑Crystal Manifest\n\n' > "$MAN"

rid="${TAU_RECEIPT_ID:-unknown}"
rhash="${TAU_RECEIPT_HASH:-unknown}"
plan="${TAU_PLAN:-FREE}"
ts="$(date -u +'%Y-%m-%dT%H:%M:%SZ')"

line="STATUS: ${ts} • plan=${plan} • receipt=${rid} • hash=${rhash}"

if grep -q '^STATUS:' "$MAN"; then
  # portable in-place edit (GNU/BSD)
  if sed --version >/dev/null 2>&1; then
    sed -i -E "s|^STATUS:.*$|${line}|" "$MAN"
  else
    sed -i '' -E "s|^STATUS:.*$|${line}|" "$MAN"
  fi
else
  printf '\n%s\n' "$line" >> "$MAN"
fi

printf '[manifest] %s\n' "$line" >&2
