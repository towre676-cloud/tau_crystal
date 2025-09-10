#!/usr/bin/env bash
set -Eeuo pipefail
set +H
umask 022

usage(){ echo "usage: save_request_preimage.sh <stem> <file|->" >&2; exit 2; }

stem="${1:-}"; src="${2:-}"
[ -n "$stem" ] || usage
[ -n "$src" ]  || usage

out="analysis/${stem}.request.canon.json"
mkdir -p analysis

# write bytes exactly
if [ "$src" = "-" ]; then
  tmp="$(mktemp)"
  cat > "$tmp"
  [ -s "$tmp" ] || { echo "[err] no bytes on stdin" >&2; rm -f "$tmp"; exit 3; }
  mv "$tmp" "$out"
else
  [ -f "$src" ] && [ -s "$src" ] || { echo "[err] empty or missing: $src" >&2; exit 3; }
  cat "$src" > "$out"
fi

# pick a hash tool (use set -- to avoid awk quoting)
if command -v sha256sum >/dev/null 2>&1; then
  set -- $(sha256sum -- "$out"); h="$1"
elif command -v shasum >/dev/null 2>&1; then
  set -- $(shasum -a 256 -- "$out"); h="$1"
elif command -v openssl >/dev/null 2>&1; then
  set -- $(openssl dgst -sha256 -- "$out"); h="$2"
else
  echo "[err] no sha256 tool found (install coreutils or openssl)" >&2
  exit 127
fi

printf "%s\n" "$h"
exit 0
