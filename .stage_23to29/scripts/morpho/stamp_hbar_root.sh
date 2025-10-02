#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
PACK_DIR="${1:-}"
[ -n "$PACK_DIR" ] && [ -d "$PACK_DIR" ] || { echo "usage: $0 PACK_DIR" >&2; exit 2; }
REC="$PACK_DIR/corridor.receipt.tsv"
GLB="$PACK_DIR/global.L"
[ -f "$REC" ] || { echo "missing $REC" >&2; exit 3; }
[ -f "$GLB" ] || { echo "missing $GLB" >&2; exit 4; }
H="$(awk -F= '/^H_BAR=/{print $2}' "$GLB" | head -n1)"
if grep -q "^H_BAR=" "$REC"; then
  cur="$(awk -F= '/^H_BAR=/{print $2}' "$REC" | tail -n1)"
  if [ -z "$cur" ]; then
    awk -F= -v H="$H" 'BEGIN{done=0} /^H_BAR=/ && $2=="" && !done {print "H_BAR=" H; done=1; next} {print}' "$REC" > "$REC.tmp" && mv "$REC.tmp" "$REC"
  fi
else
  printf "H_BAR=%s\n" "$H" >> "$REC"
fi
if ! grep -q "^ROOT" "$REC"; then
  MERK="$(awk -F= '/^MERKLE_SIM=/{print $2}' "$REC" | head -n1)"
  if [ -n "$MERK" ]; then ROOT="$MERK"; else ROOT="$(sha256sum "$REC" | awk "{print \$1}")"; fi
  printf "ROOT\t%s\n" "$ROOT" >> "$REC"
else
  ROOT="$(awk '$1=="ROOT"{print $2}' "$REC" | head -n1)"
fi
COUNT="$(find "$PACK_DIR" -maxdepth 1 -type f | wc -l | awk "{print \$1}")"
echo "stamped: $PACK_DIR  (H_BAR=$H, files=$COUNT, root=$ROOT)"
