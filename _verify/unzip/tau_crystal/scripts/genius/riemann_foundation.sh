#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
idx="${1:-42}"
root=".tau_ledger/genius"; mkdir -p "$root"
t=$(ts); f="$root/riemannv1-$t.meta"
zr=0.5; zi=$(awk -v i="$idx" 'BEGIN{print i*log(i+1)}')
foundation=$(printf '%s\n' "$zr+$zi" | sha -)
: > "$f"; emit_kv schema taucrystal/riemann/v1 "$f"; emit_kv id "$(basename "${f%.meta}")" "$f"; emit_kv utc "$t" "$f"; emit_kv zero_index "$idx" "$f"; emit_kv zero_value "$zr+$zi" "$f"; emit_kv hash_foundation "$foundation" "$f"; emit_kv hypothesis_assumed true "$f"
echo "[OK] riemann: $f"
