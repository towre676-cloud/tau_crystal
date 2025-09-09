#!/usr/bin/env bash
set -euo pipefail
file="${1:?usage: hash.sh <file>}"
if command -v b3sum >/dev/null 2>&1; then
  b3sum "$file" | awk '{print $1" blake3"}'
else
  sha256sum "$file" | awk '{print $1" sha256"}'
fi
