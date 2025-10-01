#!/usr/bin/env bash
set -euo pipefail
STATUS="analysis/freed/STATUS.md"
mkdir -p analysis/freed
[ -f "$STATUS" ] || printf "# Freed RG — Completion Status\n" > "$STATUS"

# remove all previous blocks
TMP="$(mktemp)"
awk '
BEGIN{drop=0}
/^## New Receipts \(this run\)/ { drop=1; next }
(drop==1 && /^## /){ drop=0 }
(drop==1){ next }
{ print }
' "$STATUS" > "$TMP" && mv "$TMP" "$STATUS"

# append fresh block from current files
{
  printf "\n## New Receipts (this run)\n\n"
  printf "| Kind | File |\n|------|------|\n"
  find analysis/freed -maxdepth 1 -type f -name '*_receipt.json' -print \
    | sort -u \
    | while read -r f; do
        base="$(basename "${f%_receipt.json}")"
        printf "| %s | %s |\n" "$base" "$f"
      done
} >> "$STATUS"
