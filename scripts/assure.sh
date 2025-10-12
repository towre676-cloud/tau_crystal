#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C
cmd="${1:-run}"
ts=$(date -u +%Y%m%dT%H%M%SZ)
mkdir -p .tau_ledger
tree_sha=$(git ls-files -z | xargs -0 sha256sum | sort -k2,2 | sha256sum | awk "{print \$1}")
py=$(python -V 2>&1 | awk "{print \$2}")
lean=$(lean --version 2>/dev/null | head -n1 | awk "{print \$2}")
recs=$(find .tau_ledger -type f -name "*.receipt" 2>/dev/null | wc -l | tr -d " ")
json=$(printf "{\"ts\":\"%s\",\"tree_sha256\":\"%s\",\"python\":\"%s\",\"lean\":\"%s\",\"receipts\":%s}\n" "$ts" "$tree_sha" "$py" "$lean" "$recs")
case "$cmd" in
  --mint-manifest|mint-manifest) printf "%s\n" "$json";;
  *) printf "%s\n" "$json" > .tau_ledger/manifest_current.json; printf "OK\n";;
esac
