#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
roothash=".tau_ledger/self/root.sha256"; chain=".tau_ledger/timechain/chain.tsv"
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
filter() { git ls-files | grep -E "^(scripts/|analysis/|metrics/|bootstrap/|docs/|TauCrystal/|Core/)" || true; }
hash=$(filter | xargs -r -I{} sha256sum "{}" | awk "{print \$1}" | sort | sha256sum | awk "{print \$1}")
mkdir -p "$(dirname "$roothash")" "$(dirname "$chain")"
prev="GENESIS" ; [ -s "$chain" ] && prev=$(tail -n 1 "$chain" | cut -f3)
link=$(printf "%s\n" "$prev$hash$ts" | sha256sum | awk "{print \$1}")
[ -s "$roothash" ] || printf "%s\n" "$hash" > "$roothash"
base=$(cat "$roothash" 2>/dev/null || echo "")
printf "%s\t%s\t%s\n" "$ts" "$hash" "$link" >> "$chain"
if [ "$hash" != "$base" ]; then echo "[self] drift: baseline $base now $hash"; exit 1; fi
echo "[self] ok $hash"; exit 0
