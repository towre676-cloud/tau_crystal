#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
out=".tau_ledger/metrics/monodromy.json"; mkdir -p "$(dirname "$out")"
base="${1:-env.base.json}"; loop="${2:-env.loop.json}"
[ -s ".tau_ledger/env/$base" ] && [ -s ".tau_ledger/env/$loop" ] || { echo "{\"monodromy\":null,\"error\":\"missing env snapshots\"}" > "$out"; echo "$out"; exit 0; }
bsha=$(scripts/meta/_sha256.sh ".tau_ledger/env/$base" 2>/dev/null || openssl dgst -sha256 ".tau_ledger/env/$base" | awk "{print \$2}")
lsha=$(scripts/meta/_sha256.sh ".tau_ledger/env/$loop" 2>/dev/null || openssl dgst -sha256 ".tau_ledger/env/$loop" | awk "{print \$2}")
if command -v jq >/dev/null 2>&1; then
  diffc=$(jq -S . ".tau_ledger/env/$base" | sha256sum | awk "{print \$1}")
  diffl=$(jq -S . ".tau_ledger/env/$loop" | sha256sum | awk "{print \$1}")
else
  diffc="$bsha"; diffl="$lsha"
fi
printf "{\\"monodromy\\":{\\"base_hash\\":\\"%s\\",\\"loop_hash\\":\\"%s\\",\\"transport\\":\\"%s->%s\\"}}\n" "$diffc" "$diffl" "$diffc" "$diffl" > "$out"
echo "$out"
