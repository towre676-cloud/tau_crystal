#!/usr/bin/env bash
set +H; umask 022

# Usage: face15_ingest.sh <IN_DIR> <OUT_DIR>
IN="$1"; OUT="$2"

[ -n "$IN" ] && [ -d "$IN" ] || { echo "[[ingest]] ERROR: invalid IN: '$IN'"; exit 2; }
[ -n "$OUT" ] || { echo "[[ingest]] ERROR: missing OUT"; exit 2; }

# Create OUT if missing; don't treat "exists" as an error
mkdir -p "$OUT" || true

# Mirror tree and copy files (overwrites OK)
( cd "$IN"  && find . -type d -print0 | xargs -0 -I{} mkdir -p "$OUT/{}" )
( cd "$IN"  && find . -type f -print0 | xargs -0 -I{} cp -f "{}" "$OUT/{}" )

echo "[[ingest]] ok: '$IN' -> '$OUT'"
exit 0
