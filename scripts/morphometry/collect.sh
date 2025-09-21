#!/usr/bin/env bash
set -euo pipefail
set +H
root="$(cd "$(dirname "$0")/../.." && pwd)"
out="$root/_fusion_out/morphometry"
mkdir -p "$out"
copy_one(){ src="$1"; base="$(basename "$src")"; dst="$out/$base"; cp -p "$src" "$dst" 2>/dev/null || true; }
for pat in \\
  "$root/.tau_ledger/discovery/"*.json \\
  "$root/analysis/morpho/"*.json \\
  "$root/receipts/morpho/"*.json \\
  "$root/ls3dw_out/"*.json \\
  "$root/ls3dw_out/"*/*.json \\
; do
  for f in $pat; do [ -f "$f" ] && copy_one "$f"; done
done
idx="$out/index.txt"; : > "$idx"
for g in "$out"/*.json; do [ -f "$g" ] || continue; bytes=$(wc -c < "$g" | tr -d " "); echo "$(date -u +%Y-%m-%dT%H:%M:%SZ)  $(basename "$g")  ${bytes}B" >> "$idx"; done
echo "[morphometry] collected -> $out"
