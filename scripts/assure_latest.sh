#!/usr/bin/env bash
set -euo pipefail

latest="receipts/latest.txt"
# If latest missing, use newest receipt on disk
if [ ! -f "$latest" ]; then
  newest="$(ls -1 receipts/receipt-*.txt 2>/dev/null | tail -n1 || true)"
  [ -n "${newest:-}" ] && cp "$newest" "$latest"
fi

if [ -f "$latest" ]; then
  sed -n '1,4p' "$latest"
else
  echo "[err] no receipts yet"
fi
