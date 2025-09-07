#!/usr/bin/env bash
set -euo pipefail
f="${1:-docs/manifest.md}"
out="${2:-${f%.*}.sha256}"

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum "$f" > "$out"
elif command -v shasum >/dev/null 2>&1; then
  shasum -a 256 "$f" > "$out"
elif [[ "${OS:-}" == "Windows_NT" ]] && command -v certutil >/dev/null 2>&1; then
  certutil -hashfile "$f" SHA256 | awk 'NR==2{print $1 " *" f}' f="$f" > "$out"
else
  echo "No SHA-256 tool found." >&2; exit 1
fi
echo "Wrote $out"
