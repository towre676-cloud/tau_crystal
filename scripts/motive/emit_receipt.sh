#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ID="${1:?motive id}"
BASE="analysis/motive/objects/$ID"
[ -d "$BASE" ] || { echo "[err] missing $BASE" >&2; exit 1; }
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
REC_DIR="analysis/motive/receipts"; mkdir -p "$REC_DIR"
MAP="$REC_DIR/$ID.$STAMP.map"; : > "$MAP"
find "$BASE" -type f | LC_ALL=C sort > "$MAP"
HASHES="$REC_DIR/$ID.$STAMP.hashes"; : > "$HASHES"
scripts/meta/_sha256.sh $(cat "$MAP") | LC_ALL=C sort > "$HASHES"
MERKLE="$(awk '{print $1}' "$HASHES" | tr -d '\r' | {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum | awk '{print $1}';
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 | awk '{print $1}';
  else python -c "import sys,hashlib; print(hashlib.sha256(sys.stdin.buffer.read()).hexdigest())"; fi
})"
OUT="$REC_DIR/$ID.$STAMP.receipt.json"; : > "$OUT"
printf "{\n  \"id\":\"%s\",\n  \"stamp\":\"%s\",\n  \"merkle\":\"%s\",\n  \"files\":[\n" "$ID" "$STAMP" "$MERKLE" >> "$OUT"
sep=""; while read -r H F; do printf "%s  {\"sha256\":\"%s\",\"path\":\"%s\"}\n" "$sep" "$H" "$F" >> "$OUT"; sep=",\n"; done < "$HASHES"
printf "%s\n" "]\n}" >> "$OUT"
echo "$OUT"
