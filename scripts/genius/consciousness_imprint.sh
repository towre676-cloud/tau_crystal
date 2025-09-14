#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
root=".tau_ledger/genius"; mkdir -p "$root"; t=$(ts); id="consciousv1-$t"; meta="$root/$id.meta"
vals=$(sed -n "s/^tau: //p" "$root"/entangle-*.meta 2>/dev/null | tr "\n" " " || true)
set +e; cnt=$(wc -w <<< "$vals" | tr -d " "); set -e; [ "$cnt" -gt 0 ] || vals="0 0 0 0"
sum=0; for v in $vals; do sum=$(echo "$sum + $v" | bc -l); done
avg=$(echo "scale=10; $sum / ($cnt + 0.0000001)" | bc -l)
var=0; for v in $vals; do var=$(echo "$var + ($v - $avg)^2" | bc -l); done
var=$(echo "scale=10; $var / ($cnt + 0.0000001)" | bc -l)
: > "$meta"; emit_kv "schema" "taucrystal/conscious/v1" "$meta"; emit_kv "id" "$id" "$meta"; emit_kv "utc" "$t" "$meta"; emit_kv "variance" "$var" "$meta"; emit_kv "is_deterministic" "$(echo "$var < 0.001" | bc -l)" "$meta"; echo "[OK] conscious: $meta"
