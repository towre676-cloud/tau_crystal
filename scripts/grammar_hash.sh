#!/usr/bin/env bash
set -euo pipefail
GRAMMAR_FILE="${GRAMMAR_FILE:-verify/ReceiptGrammar.lean}"
if [ ! -s "$GRAMMAR_FILE" ]; then
  echo "[warn] missing $GRAMMAR_FILE; using 'unknown'"; printf "unknown unknown\n"; exit 0
fi
"$(dirname "$0")/hash.sh" "$GRAMMAR_FILE"
