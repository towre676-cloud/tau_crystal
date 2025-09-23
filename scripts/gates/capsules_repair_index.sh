#!/usr/bin/env bash
set -euo pipefail; umask 022
source scripts/capsule/merkle_lib.sh
idx=".tau_ledger/capsules.tsv"
[ -f "$idx" ] || { echo "[CAPREPAIR] no index"; exit 0; }
tmp="$(mktemp)"; cp "$idx" "$tmp"; : > "$idx"

while IFS=$'\t' read -r family capsule oldroot receipt; do
  [ -n "${family:-}" ] || continue
  dir="$(dirname "$receipt")"
  if [ ! -d "$dir" ]; then
    echo -e "$family\t$capsule\t$oldroot\t$receipt" >> "$idx"; continue
  fi
  # boundary guard
  if [ -f "$dir/boundary.txt" ] && [ -f "$dir/boundary.sig" ]; then
    got=$(sha256sum "$dir/boundary.txt" | awk '{print $1}')
    want=$(awk '{print $1}' "$dir/boundary.sig")
    if [ "$got" != "$want" ]; then
      echo "[CAPREPAIR] skip (boundary mismatch) $capsule"
      echo -e "$family\t$capsule\t$oldroot\t$receipt" >> "$idx"; continue
    fi
  fi
  newroot="$(merkle__dir_root "$dir")"
  if [ "$newroot" != "$oldroot" ]; then
    echo "[CAPREPAIR] rewrite root $capsule old=$oldroot new=$newroot"
    utc="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    printf '{\n  "capsule":"%s",\n  "utc":"%s",\n  "merkle_root":"%s"\n}\n' "$(basename "$dir")" "$utc" "$newroot" > "$dir/capsule.receipt.json"
    echo -e "$family\t$capsule\t$newroot\t$receipt" >> "$idx"
  else
    echo -e "$family\t$capsule\t$oldroot\t$receipt" >> "$idx"
  fi
done < "$tmp"
rm -f "$tmp"
echo "[CAPREPAIR] done"
