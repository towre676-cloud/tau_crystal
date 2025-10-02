#!/usr/bin/env bash
set +H
umask 022
COR="analysis/validation/corridor.receipt.tsv"
mkdir -p analysis/validation
touch "$COR"
awk '{ sub(/\r$/,""); print }' "$COR" > "$COR.tmp" && mv "$COR.tmp" "$COR"
if ! grep -q "^op_return_hex=" "$COR"; then
  SHA=$(sha256sum analysis/validation/SIGNED_DATASET.bin 2>/dev/null | awk "{print \$1}")
  if [ -n "$SHA" ]; then printf "op_return_hex=6a20%s\n" "$SHA" >> "$COR"; fi
fi
if ! grep -q "^txid=" "$COR"; then printf "txid=\n" >> "$COR"; fi
if ! grep -q "^block=" "$COR"; then printf "block=\n" >> "$COR"; fi
printf "stamped: %s\n" "$COR"
