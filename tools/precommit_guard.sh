#!/usr/bin/env bash
set -euo pipefail
# Refuse CR bytes in tracked text files
if git ls-files -z | xargs -0 grep -nIU $'\r' -- || false; then
  echo "[err] CR (\\r) detected in tracked files; convert to LF" >&2
  exit 10
fi
# Shell syntax check on changed *.sh
changed="$(git diff --cached --name-only | grep -E '\.sh$' || true)"
if [ -n "$changed" ]; then
  echo "$changed" | while read -r f; do
    [ -f "$f" ] && bash -n "$f" || true
  done
fi
exit 0
