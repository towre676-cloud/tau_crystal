#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
mkdir -p "$ROOT/out/receipts"
: > "$ROOT/out/receipts/_concat.bin"
for f in "$ROOT/out/coeffs/q1_stub.json" "$ROOT/out/receipts/automorphy.json" "$ROOT/out/receipts/mde.json"; do
  [ -f "$f" ] && cat "$f" >> "$ROOT/out/receipts/_concat.bin"
done
sha256sum "$ROOT/out/receipts/_concat.bin" | awk '{print $1}' > "$ROOT/out/receipts/merkle_root.txt"
echo "MERKLE_ROOT=$(cat "$ROOT/out/receipts/merkle_root.txt")"
