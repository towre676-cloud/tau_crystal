#!/usr/bin/env bash
set -euo pipefail
file="${GRAMMAR_FILE:-verify/ReceiptGrammar.lean}"
if [ -f "$file" ]; then
  exec scripts/hash.sh "$file"
else
  echo "unknown none"
fi
