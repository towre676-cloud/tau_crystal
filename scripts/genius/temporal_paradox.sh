#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
future="${1:-20260914T000000Z}"; root=".tau_ledger/genius"; mkdir -p "$root"; t=$(ts); id="paradoxv1-$t"; meta="$root/$id.meta"
commit=$(printf "%s\n" "$future-$RANDOM" | sha -)
: > "$meta"; emit_kv "schema" "taucrystal/paradox/v1" "$meta"; emit_kv "id" "$id" "$meta"; emit_kv "utc" "$t" "$meta"; emit_kv "future" "$future" "$meta"; emit_kv "commitment" "$commit" "$meta"
now=$(ts); if [ "$now" \> "$future" ]; then echo "[warn] future has arrived; attach a resolver check here"; fi
echo "[OK] paradox commit: $meta"
