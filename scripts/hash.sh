#!/usr/bin/env bash
set -euo pipefail
f="${1:?usage: hash.sh <file>}"
if command -v b3sum >/dev/null 2>&1; then algo=blake3; dig="$(b3sum "$f" | awk '{print $1}')"
else algo=sha256; dig="$(sha256sum "$f" | awk '{print $1}')"; fi
printf "%s %s\n" "$dig" "$algo"
