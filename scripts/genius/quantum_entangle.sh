#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
n="${1:-2}"; root=".tau_ledger/genius"; mkdir -p "$root"; t=$(ts)
hidden=$(printf "%s\n" "$t-$RANDOM" | sha -)
for i in $(seq 1 "$n"); do
  ang=$(echo "scale=10; (a(1)*$i)/2" | bc -l)
  tauv=$(echo "scale=10; s($ang)^2" | bc -l)
  meta="$root/entangle-$t-$i.meta"; : > "$meta"
  emit_kv "schema" "taucrystal/entangle/v1" "$meta"; emit_kv "id" "entangle-$t-$i" "$meta"
  emit_kv "utc" "$t" "$meta"; emit_kv "hidden" "$hidden" "$meta"; emit_kv "angle" "$ang" "$meta"; emit_kv "tau" "$tauv" "$meta"
done; echo "[OK] entangled: $n"
