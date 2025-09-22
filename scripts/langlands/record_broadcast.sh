#!/usr/bin/env bash
set +H
umask 022
COR="analysis/validation/corridor.receipt.tsv"
TXID="$1"; BLK="$2"
[ -z "$TXID" ] && { echo "usage: $0 <txid> <block_height_or_hash>" >&2; exit 2; }
touch "$COR"
awk '{sub(/\r$/,""); print}' "$COR" > "$COR.tmp" && mv "$COR.tmp" "$COR"
sed -i "/^txid=/d" "$COR" 2>/dev/null || true
sed -i "/^block=/d" "$COR" 2>/dev/null || true
printf "txid=%s\n" "$TXID" >> "$COR"
[ -n "$BLK" ] && printf "block=%s\n" "$BLK" >> "$COR" || true
echo "updated $COR with txid and block"
