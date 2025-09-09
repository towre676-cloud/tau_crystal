#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022
ASSUME_FILE="${ASSUME_FILE:-.tau_ledger/assumptions.tsv}"
WHITELIST_DIR="${WHITELIST_DIR:-boundary}"
ENFORCE="${BOUNDARY_ENFORCE:-0}"
warns=0
summary(){ if [ -n "${GITHUB_STEP_SUMMARY:-}" ] && [ -w "$GITHUB_STEP_SUMMARY" ]; then printf "%s\n" "$*" >> "$GITHUB_STEP_SUMMARY" || true; fi; }
echo "[boundary] reading $ASSUME_FILE"
[ -f "$ASSUME_FILE" ] || { echo "[boundary] no assumptions file; nothing to check"; summary "Boundary check: no assumptions file found. ✅"; exit 0; }

# build a flat whitelist file from boundary/WHITELIST* (ignore blanks/comments)
patfile="$(mktemp -t whitelist.XXXXXX || mktemp -u)"
: > "$patfile"
for f in "$WHITELIST_DIR"/WHITELIST*; do
  [ -f "$f" ] || continue
  # strip comments and empty lines
  while IFS= read -r line; do
    case "$line" in ""|\#*) continue ;; esac
    printf "%s\n" "$line" >> "$patfile"
  done < "$f"
done
echo "[boundary] whitelist patterns: $(wc -l < "$patfile" 2>/dev/null || echo 0)"
: > boundary_report.txt
TAB=$'\t'
while IFS=$'\t' read -r key rest || [ -n "${key:-}" ]; do
  [ -n "${key//[[:space:]]/}" ] || continue
  case "$key" in \#*) continue ;; esac
  allowed=0
  while IFS= read -r p || [ -n "${p:-}" ]; do
    [ -n "$p" ] || continue
    case "$key" in
      '$p') allowed=1 ;;
    esac
    [ "$allowed" -eq 1 ] && break
  done < "$patfile"
  if [ "$allowed" -eq 0 ]; then
    printf "[boundary][violation] %s\t%s\n" "$key" "${rest:-}" | tee -a boundary_report.txt
    warns=$((warns+1))
  fi
done < "$ASSUME_FILE"
rm -f "$patfile" 2>/dev/null || true

if [ "$warns" -gt 0 ]; then
  summary "### Boundary check warnings\nFound $warns assumption(s) not whitelisted. See \`boundary_report.txt\` in artifacts or job logs."
  echo "[boundary] $warns violation(s) found"
  if [ "$ENFORCE" = "1" ]; then echo "[boundary] enforcement on; failing"; exit 1; else echo "[boundary] warn-only; passing"; exit 0; fi
else
  summary "Boundary check: clean. ✅"
  echo "[boundary] clean"
  exit 0
fi
