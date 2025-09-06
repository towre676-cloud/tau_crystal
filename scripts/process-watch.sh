#!/usr/bin/env bash
set -u
INFILE="${1:-tmp/P2P.ndjson}"
CURSOR="tmp/.cursor.size"
: "${TAU_MIN:=0.06}"
: "${TAU_SLOPE:=0.30}"
export TAU_MIN TAU_SLOPE
mkdir -p tmp
[ -f "$CURSOR" ] || echo 0 > "$CURSOR"
echo "[watch] watching $INFILE (Ctrl+C to stop)"
while true; do
  sz=$(wc -c < "$INFILE" 2>/dev/null || echo 0)
  last=$(cat "$CURSOR" 2>/dev/null || echo 0)
  if [ "$sz" != "$last" ]; then
    echo "[watch] change detected ($last → $sz); processing…"
    scripts/process-once.sh "$INFILE" >/dev/null 2>&1 || true
    echo "$sz" > "$CURSOR"
  fi
  sleep 1
done
