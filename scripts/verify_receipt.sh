#!/usr/bin/env bash
set -euo pipefail
repo="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$repo"

r="${1:-receipts/latest.txt}"
if [ ! -f "$r" ]; then
  newest="$(ls -1 receipts/receipt-*.txt 2>/dev/null | tail -n1 || true)"
  [ -n "${newest:-}" ] && r="$newest"
fi

[ -f "$r" ] || { echo "[err] no receipt found"; exit 1; }

echo "[info] showing $r"
sed -n '1,4p' "$r"

# best-effort HEAD consistency check (non-fatal)
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  got="$(sed -n '1s/^HEAD: //p' "$r")"
  cur="$(git rev-parse HEAD 2>/dev/null || true)"
  [ -n "$got" ] && [ -n "$cur" ] && {
    if [[ "$got" == "$cur"* ]]; then
      echo "[ok] receipt HEAD prefixes current HEAD"
    else
      echo "[warn] receipt HEAD != current HEAD ($cur)"
    fi
  }
fi
