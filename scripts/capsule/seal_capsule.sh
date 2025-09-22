#!/usr/bin/env bash
# seal_capsule.sh <capsule_dir>
set -euo pipefail; umask 022
dir="${1:?capsule_dir}"; [ -d "$dir" ] || { echo "[CAPSEAL] not a dir: $dir"; exit 2; }

# boundary (idempotent)
b="$dir/boundary.txt"; sig="$dir/boundary.sig"
if [ ! -f "$b" ]; then
  echo "capsule=$(basename "$dir") UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$b"
fi
if [ ! -f "$sig" ]; then
  sha=$(sha256sum "$b" | awk '{print $1}')
  printf "%s  %s\n" "$sha" "$(basename "$b")" > "$sig"
fi

# collect files (exclude receipt itself)
mapfile -t rels < <(LC_ALL=C find "$dir" -type f ! -name 'capsule.receipt.json' -printf '%P\n' | LC_ALL=C sort)

# compute leaf hashes
leaves=()
for rel in "${rels[@]}"; do
  h=$(sha256sum "$dir/$rel" | awk '{print $1}')
  leaves+=("$h")
done

# fold to a single root (if none, use 64 zeros)
if [ ${#leaves[@]} -eq 0 ]; then
  root=$(printf '0%.0s' {1..64})
else
  layer=("${leaves[@]}")
  while :; do
    if [ ${#layer[@]} -eq 1 ]; then
      root="${layer[0]}"
      break
    fi
    next=()
    i=0
    while [ $i -lt ${#layer[@]} ]; do
      if [ $((i+1)) -lt ${#layer[@]} ]; then
        pair="${layer[$i]}${layer[$((i+1))]}"
      else
        pair="${layer[$i]}"
      fi
      h=$(printf '%s' "$pair" | sha256sum | awk '{print $1}')
      next+=("$h")
      i=$((i+2))
    done
    layer=("${next[@]}")
  done
fi

utc="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
rec="$dir/capsule.receipt.json"
# minimal stable JSON
printf '{\n  "capsule":"%s",\n  "utc":"%s",\n  "merkle_root":"%s"\n}\n' \
  "$(basename "$dir")" "$utc" "$root" > "$rec"
echo "[CAPSEAL] merkle_root=$root"

# global index
idx=".tau_ledger/capsules.tsv"; mkdir -p "$(dirname "$idx")"
family="$(basename "$dir" | cut -d- -f1)"
printf "%s\t%s\t%s\t%s\n" "$family" "$(basename "$dir")" "$root" "$rec" >> "$idx"
echo "[CAPSEAL] indexed $family $(basename "$dir")"
