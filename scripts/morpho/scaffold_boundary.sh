#!/usr/bin/env bash
set -euo pipefail; umask 022
pack="$1"
[ -d "$pack" ] || { echo "[BOUNDARY] no pack dir: $pack"; exit 2; }
b="$pack/boundary.txt"; s="$pack/boundary.sig"
if [ ! -f "$b" ]; then
  {
    echo "# morpho boundary (redaction + provenance)"
    echo "PACK=$(basename "$pack")"
    echo "UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    [ -d "$pack/PRIVATE images" ] && echo "REDACT=PRIVATE images/" || true
    [ -d "$pack/PRIVATE" ] && echo "REDACT=PRIVATE/" || true
  } > "$b"
  echo "[BOUNDARY] wrote $b"
fi
if [ ! -f "$s" ]; then
  sha=$(sha256sum "$b" | awk '{print $1}')
  printf "%s  %s\n" "$sha" "$(basename "$b")" > "$s"
  echo "[BOUNDARY] wrote $s (sha256)"
fi
