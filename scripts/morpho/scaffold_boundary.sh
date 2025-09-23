#!/usr/bin/env bash
set -euo pipefail; umask 022
pack="${1:?pack dir}"
[ -d "$pack" ] || { echo "[BOUNDARY] not a dir: $pack"; exit 2; }
b="$pack/boundary.txt"; s="$pack/boundary.sig"
{
  echo "# morpho boundary (redaction + provenance)"
  echo "PACK=$(basename "$pack")"
  echo "UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  [ -d "$pack/PRIVATE images" ] && echo "REDACT=PRIVATE images/" || true
  [ -d "$pack/PRIVATE" ] && echo "REDACT=PRIVATE/" || true
} > "$b"
sha=$(sha256sum "$b" | awk '{print $1}')
printf "%s  %s\n" "$sha" "$(basename "$b")" > "$s"
echo "[BOUNDARY] scaffolded $(basename "$pack")"
