#!/usr/bin/env bash
set -euo pipefail
set +H
tool=${1:-}; inp=${2:-}; out=${3:-}
mkdir -p "$(dirname -- "${out:-/dev/null}")" 2>/dev/null || true
echo "[tau_step] tool=$tool inp=$inp out=$out" >&2
if [ -n "${inp:-}" ] && [ -f "$inp" ]; then
  # compute a simple digest (openssl is standard in Git Bash); fallback to size only
  if command -v openssl >/dev/null 2>&1; then dgst=$(openssl dgst -sha1 "$inp" | awk "{print \$2}"); else dgst=$(wc -c <"$inp" | tr -d " "); fi
  printf "%s\n" "tool=$tool inp=$inp out=$out sha1=${dgst:-na}"
  "tool": "",
  "sha1": "na"
  [ -n "${out:-}" ] && printf "%s\n" "}" > "$out"
else
  echo "[tau_step] WARN: input file not found: $inp" >&2
  printf "%s\n" "tool=$tool inp=$inp out=$out (no input found)"
  "tool": "",
  "note": "input missing"
  [ -n "${out:-}" ] && printf "%s\n" "}" > "$out"
fi
