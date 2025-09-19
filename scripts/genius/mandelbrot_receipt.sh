#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
root=".tau_ledger/genius"; mkdir -p "$root"; t=$(ts); id="mandelbrotv1-$t"; meta="$root/$id.meta"
seed="${1:-$t}"; sdig=$(printf "%s\n" "$seed" | sha -)
cre=$(echo "scale=10; 0."$(printf "%s" "$sdig" | cut -c1-6))
cim=$(echo "scale=10; 0."$(printf "%s" "$sdig" | cut -c7-12))
zr=0; zi=0; er=2; max=1000; it=0
while [ $(echo "$zr*$zr + $zi*$zi <= $er*$er" | bc -l) -eq 1 ] && [ $it -lt $max ]; do
  nr=$(echo "$zr*$zr - $zi*$zi + $cre" | bc -l); ni=$(echo "2*$zr*$zi + $cim" | bc -l); zr="$nr"; zi="$ni"; it=$((it+1))
done
: > "$meta"; emit_kv "schema" "taucrystal/mandelbrot/v1" "$meta"; emit_kv "id" "$id" "$meta"; emit_kv "utc" "$t" "$meta"; emit_kv "seed" "$seed" "$meta"; emit_kv "escape_iter" "$it" "$meta"; echo "[OK] mandelbrot: $meta"
