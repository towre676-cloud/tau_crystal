#!/usr/bin/env bash
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
OUT=".tau_ledger/git/git_head.txt"
if command -v git >/dev/null 2>&1 && git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  { echo "utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)";
    echo "rev=$(git rev-parse HEAD 2>/dev/null || echo NA)";
    echo "branch=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo NA)";
    echo "remote=$(git config --get remote.origin.url 2>/dev/null || echo NA)";
    echo "dirty=$(git status --porcelain 2>/dev/null | wc -l | tr -d \"[:space:]\r\")";
  } > "$OUT"
else
  { echo "utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"; echo "rev=NA"; echo "branch=NA"; echo "remote=NA"; echo "dirty=NA"; } > "$OUT"
fi
echo "[ok] wrote $OUT"
