#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
dir=".tau_ledger/holo"; mkdir -p "$dir"
set -- .tau_ledger/receipts/*.json
[ -e "$1" ] || { echo "[skip] no receipts"; exit 0; }
ts=$(date -u +%Y%m%dT%H%M%SZ); out="$dir/holov1-$ts.json"
{
  printf '{\n'
  printf '  "schema":"taucrystal/holo/v1","id":"holov1-%s","utc":"%s","receipts":[' "$ts" "$ts"
  first=1
  for r in .tau_ledger/receipts/*.json; do
    sha=$(sha256sum "$r" | awk '{print $1}')
    if [ $first -eq 1 ]; then first=0; printf '\n'; else printf ',\n'; fi
    printf '    {"file":"%s","sha256":"%s"}' "$(basename "$r")" "$sha"
  done
  printf '\n  ]\n}\n'
} > "$out"
echo "[OK] holo: $out"
