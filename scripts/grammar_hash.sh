#!/usr/bin/env bash
set -euo pipefail
GRAMMAR_FILE="${GRAMMAR_FILE:-verify/ReceiptGrammar.lean}"
if [ -s "$GRAMMAR_FILE" ]; then
  if command -v b3sum >/dev/null 2>&1; then
    b3sum "$GRAMMAR_FILE" | awk '{print $1" blake3"}'
  else
    sha256sum "$GRAMMAR_FILE" | awk '{print $1" sha256"}'
  fi
else
  echo "unknown unknown"
fi
