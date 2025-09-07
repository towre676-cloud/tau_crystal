#!/usr/bin/env bash
set -euo pipefail
src="${1:-docs/manifest.md}"
html="${2:-docs/tau-crystal.html}"

if ! command -v pandoc >/dev/null 2>&1; then
  echo "pandoc not found on PATH." >&2
  exit 1
fi

pandoc "$src" -o "$html" --standalone \
  --css=https://cdn.jsdelivr.net/npm/water.css@2/out/water.css

echo "Wrote $html"
