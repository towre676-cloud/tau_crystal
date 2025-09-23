#!/usr/bin/env bash
set -euo pipefail; umask 022
shopt -s nullglob
arr=( .tau_ledger/entropy/entv1-*.json )
[ "${#arr[@]}" -ge 2 ] || { echo "[ENTROPY] not enough entries"; exit 0; }
# pick 2 most recent by name (they encode UTC)
a="${arr[${#arr[@]}-2]}"; b="${arr[${#arr[@]}-1]}"
# jq required
v1=$(jq -r '.delta // .Delta // .dH // 0' "$a")
v2=$(jq -r '.delta // .Delta // .dH // 0' "$b")
inc=$(awk -v x="$v1" -v y="$v2" 'BEGIN{print (y>x)?"1":"0"}')
if [ "$inc" = "1" ]; then
  echo "[ENTROPY] increased ΔH_τ from $v1 to $v2 ($a -> $b)"
  exit 2
fi
echo "[ENTROPY] ok ($v1 → $v2)"
