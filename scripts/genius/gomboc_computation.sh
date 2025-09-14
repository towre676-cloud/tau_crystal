#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
root=".tau_ledger/genius"; mkdir -p "$root"; t=$(ts); id="gombocv1-$t"; meta="$root/$id.meta"
inp="${1:-$t}"; st="1.618"; state=$(printf "%s\n" "$inp" | sha -)
iter=0; while [ "$iter" -lt 64 ]; do grav=$(echo "scale=10; e($st/10)" | bc -l); state=$(printf "%s\n" "$state$grav" | sha -); st=$(echo "scale=10; $st - 0.01" | bc -l); iter=$((iter+1)); done
: > "$meta"; emit_kv "schema" "taucrystal/gomboc/v1" "$meta"; emit_kv "id" "$id" "$meta"; emit_kv "utc" "$t" "$meta"; emit_kv "stable_state" "$state" "$meta"; echo "[OK] gomboc: $meta"
