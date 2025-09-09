#!/usr/bin/env bash
set -euo pipefail
g="${GRAMMAR_FILE:-verify/ReceiptGrammar.lean}"
if [ -s "$g" ]; then
  if command -v b3sum >/dev/null 2>&1; then b3sum "$g" | awk '{print $1" blake3"}'
  else sha256sum "$g" | awk '{print $1" sha256"}'; fi
else
  echo "unknown unknown"
fi
