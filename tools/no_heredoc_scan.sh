#!/usr/bin/env bash
set -euo pipefail
shopt -s nullglob
PATTERN='(^|[[:space:];|&])<<-?[[:space:]]*[A-Za-z_][A-Za-z0-9_]*([[:space:]]|$)'
mapfile -t STAGED < <(git diff --cached --name-only --diff-filter=ACMRTUXB || true)
(( ${#STAGED[@]} )) || { echo "[scan] nothing staged; skipping"; exit 0; }
EXIT=0
for f in "${STAGED[@]}"; do
  case "$f" in
    .github/workflows/*.yml|.github/workflows/*.yaml|.github/actions/*) ;;
    *) continue ;;
  esac
  if grep -nE "$PATTERN" "$f" >/dev/null 2>&1; then
    echo "HERE-DOC found in $f:" >&2
    grep -nE "$PATTERN" "$f" >&2 || true
    EXIT=2
  fi
done
exit $EXIT
