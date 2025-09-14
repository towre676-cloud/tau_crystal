#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
root=".tau_ledger/genius"; mkdir -p "$root"
t=$(ts); f="$root/singularityv1-$t.meta"
gens="${1:-100}"
det=$(awk -v d=0.99 -v r=0.001 -v g="$gens" 'BEGIN{print 1 - (1-d)*exp(-r*g)}')
prox=$(awk -v d="$det" 'BEGIN{print 1/(1-d+1e-12)}')
: > "$f"; emit_kv schema taucrystal/singularity/v1 "$f"; emit_kv id "$(basename "${f%.meta}")" "$f"; emit_kv utc "$t" "$f"; emit_kv determinism "$det" "$f"; emit_kv proximity "$prox" "$f"
echo "[OK] singularity: $f"
