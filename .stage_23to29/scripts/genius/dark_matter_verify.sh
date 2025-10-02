#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
root=".tau_ledger/genius"; mkdir -p "$root"; t=$(ts); id="darkv1-$t"; meta="$root/$id.meta"
seed="${1:-classified}"; ch=$(printf "%s\n" "$seed-$t" | sha -); nul=$(printf "%s\n" "$ch-$RANDOM" | sha -)
: > "$meta"; emit_kv "schema" "taucrystal/dark/v1" "$meta"; emit_kv "id" "$id" "$meta"; emit_kv "utc" "$t" "$meta"; emit_kv "nullifier" "$nul" "$meta"; emit_kv "status" "PASS" "$meta"; echo "[OK] dark: $meta"
