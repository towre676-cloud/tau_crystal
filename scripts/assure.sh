#!/usr/bin/env bash
set -euo pipefail
umask 022

ROOT="${1:-$PWD}"
cd "$ROOT" || { echo "[err] bad root: $ROOT"; exit 1; }

LEDGER="receipts"; mkdir -p "$LEDGER"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT

# --- gather tracked files, excluding heavy/vendor stuff ---
# (git's order is stable; no need to sort)
git ls-files -z \
  -- ':!receipts/**' ':!.tau_ledger/**' ':!dist/**' ':!build/**' ':!out/**' \
  ':!node_modules/**' ':!**/__pycache__/**' ':!**/.venv/**' ':!sidecar/**' ':!rescue/**' \
  > "$TMP/files.z"

# bail if nothing to hash
if [ ! -s "$TMP/files.z" ]; then
  echo "[err] nothing to hash (no tracked files after excludes)"; exit 1
fi

# --- compute leaf hashes in deterministic path order ---
: > "$TMP/leaves"
while IFS= read -r -d '' f; do
  # skip obvious binaries by extension to keep it fast
  case "$f" in
    *.png|*.jpg|*.jpeg|*.gif|*.svg|*.mp4|*.mov|*.pdf|*.zip|*.tar|*.tar.gz|*.tgz|*.whl|*.pyd|*.dll|*.so|*.dylib|*.lib) continue ;;
  esac
  sha256sum -- "$f" | awk '{print $1}' >> "$TMP/leaves"
done < "$TMP/files.z"

# still nothing? exit
if [ ! -s "$TMP/leaves" ]; then
  echo "[err] nothing to hash (after extension filter)"; exit 1
fi

# --- merkle root (pair, duplicate last if odd) ---
mapfile -t level < "$TMP/leaves"
while [ "${#level[@]}" -gt 1 ]; do
  next=()
  last=$(( ${#level[@]} - 1 ))
  i=0
  while [ $i -le $last ]; do
    a="${level[$i]}"
    if [ $i -lt $last ]; then b="${level[$((i+1))]}"; else b="$a"; fi
    h="$(printf "%s%s" "$a" "$b" | sha256sum | awk '{print $1}')"
    next+=("$h")
    i=$((i+2))
  done
  level=("${next[@]}")
done
ROOT_HASH="${level[0]}"

# --- chain head ---
PREV="$(ls -1 "$LEDGER"/receipt-*.txt 2>/dev/null | tail -n1 || true)"
PREV_HASH="GENESIS"
[ -n "$PREV" ] && PREV_HASH="$(sed -n '1s/^HEAD: //p' "$PREV")"

HEAD="$(printf "%s|%s|%s" "$ROOT_HASH" "$PREV_HASH" "$STAMP" | sha256sum | awk '{print $1}')"

OUT="$LEDGER/receipt-$STAMP.txt"
{
  printf "HEAD: %s\n"   "$HEAD"
  printf "PREV: %s\n"   "$PREV_HASH"
  printf "MERKLE: %s\n" "$ROOT_HASH"
  printf "STATUS: user=%s host=%s stamp=%s\n" "${USER:-unknown}" "$(uname -a)" "$STAMP"
} > "$OUT"

cp "$OUT" "$LEDGER/latest.txt"

# one clean line of output (no spam)
printf "[τ] HEAD %s  ->  %s\n" "$HEAD" "$OUT"

# keep window open only if launched without a TTY (e.g., double-click)
if [ -z "${ASSURE_NO_PAUSE:-}" ] && [ ! -t 1 ]; then
  read -rp "Done. Press Enter to exit..."
fi
