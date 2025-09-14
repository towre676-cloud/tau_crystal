#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
root=".tau_ledger/genius"; mkdir -p "$root"
t=$(ts); f="$root/gombocv1-$t.meta"
state=$(printf '%s\n' "${1:-$t}" | sha -)
for i in $(seq 1 64); do state=$(printf '%s\n' "$state-$i" | sha -); done
: > "$f"; emit_kv schema taucrystal/gomboc/v1 "$f"; emit_kv id "$(basename "${f%.meta}")" "$f"; emit_kv utc "$t" "$f"; emit_kv stable_state "$state" "$f"
echo "[OK] gomboc: $f"
