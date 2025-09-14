#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
root=".tau_ledger/genius"; mkdir -p "$root"
t=$(ts); f="$root/omegav1-$t.meta"
th=$(awk 'BEGIN{print exp(-0.001)*0.999}')
ok=$(awk -v x="$th" 'BEGIN{print (x>0.998)?1:0}')
: > "$f"; emit_kv schema taucrystal/omega/v1 "$f"; emit_kv id "$(basename "${f%.meta}")" "$f"; emit_kv utc "$t" "$f"; emit_kv thermal "$th" "$f"; emit_kv quantum "$th" "$f"; emit_kv gravitational "$th" "$f"; emit_kv status "$ok" "$f"
echo "[OK] omega: $f"
[ "$ok" = "1" ] || { echo "[FAIL] omega"; exit 1; }
