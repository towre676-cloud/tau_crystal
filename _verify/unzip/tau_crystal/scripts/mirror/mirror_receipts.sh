#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
root=".tau_ledger/mirror"; mkdir -p "$root"
set -- .tau_ledger/receipts/*.json
[ -e "$1" ] || { echo "[skip] no receipts"; exit 0; }
ts=$(date -u +%Y%m%dT%H%M%SZ); f="$root/mirrorv1-$ts.meta"
: > "$f"
printf 'schema: taucrystal/mirror/v1\nid: mirrorv1-%s\nutc: %s\n' "$ts" "$ts" >> "$f"
printf 'receipts:\n' >> "$f"
for r in .tau_ledger/receipts/*.json; do
  s=$(sha256sum "$r" | awk '{print $1}')
  printf '  - %s %s\n' "$(basename "$r")" "$s" >> "$f"
done
echo "[OK] mirror: $f"
