#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
idx="${1:-42}"; root=".tau_ledger/genius"; mkdir -p "$root"; t=$(ts); id="riemannv1-$t"; meta="$root/$id.meta"
zr=0.5; zi=$(echo "scale=10; $idx*l($idx+1)" | bc -l)
foundation=$(printf "%s\n" "$zr+$zi*i" | sha -)
: > "$meta"; emit_kv "schema" "taucrystal/riemann/v1" "$meta"; emit_kv "id" "$id" "$meta"; emit_kv "utc" "$t" "$meta"; emit_kv "zero_index" "$idx" "$meta"; emit_kv "zero_value" "$zr+$zi" "$meta"; emit_kv "hash_foundation" "$foundation" "$meta"; emit_kv "hypothesis_assumed" "true" "$meta"; echo "[OK] riemann: $meta"
