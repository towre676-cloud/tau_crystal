#!/usr/bin/env bash
set -euo pipefail
f="${1:?usage: hash.sh <file>}"
if command -v b3sum >/dev/null 2>&1; then b3sum "$f" | awk '{print $1" blake3"}'
else sha256sum "$f" | awk '{print $1" sha256"}'; fi
