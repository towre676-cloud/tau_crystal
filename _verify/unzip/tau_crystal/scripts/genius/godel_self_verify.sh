#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
root=".tau_ledger/genius"; mkdir -p "$root"
t=$(ts); id="godelv1-$t"; meta="$root/$id.meta"
self_digest=$(find scripts/ -type f -name "*.sh" -print0 | xargs -0 cat | sha -)
: > "$meta"; emit_kv "schema" "taucrystal/godel/v1" "$meta"
emit_kv "id" "$id" "$meta"; emit_kv "utc" "$t" "$meta"; emit_kv "self_digest" "$self_digest" "$meta"
prev=$(ls -1 .tau_ledger/receipts/*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
if [ -n "$prev" ]; then emit_kv "prev_hash" "$(sha "$prev")" "$meta"; fi
emit_kv "self_hash" "$(selfhash "$meta")" "$meta"; echo "[OK] godel: $meta"
