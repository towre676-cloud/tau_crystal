#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
root=".tau_ledger/genius"; mkdir -p "$root"; t=$(ts); id="singularityv1-$t"; meta="$root/$id.meta"
det=0.99; rate=0.001; gens="${1:-100}"
for g in $(seq 1 "$gens"); do det=$(echo "scale=12; 1 - (1 - $det)*e(-$rate)" | bc -l); done
prox=$(echo "scale=12; 1/(1 - $det + 0.000000000001)" | bc -l)
: > "$meta"; emit_kv "schema" "taucrystal/singularity/v1" "$meta"; emit_kv "id" "$id" "$meta"; emit_kv "utc" "$t" "$meta"; emit_kv "determinism" "$det" "$meta"; emit_kv "proximity" "$prox" "$meta"; echo "[OK] singularity: $meta"
