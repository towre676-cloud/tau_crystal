#!/usr/bin/env bash
# seal_capsule.sh <capsule_dir>
set -euo pipefail; umask 022
dir="${1:?capsule_dir}"; [ -d "$dir" ] || { echo "[CAPSEAL] not a dir: $dir"; exit 2; }
# write boundary if missing
b="$dir/boundary.txt"; sig="$dir/boundary.sig"
if [ ! -f "$b" ]; then
  echo "capsule=$(basename "$dir") UTC=$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$b"
fi
[ -f "$sig" ] || { sha=$(sha256sum "$b"|awk '{print $1}'); printf "%s  %s\n" "$sha" "$(basename "$b")" > "$sig"; }

# compute Merkle root over all files except receipt itself
tmp="$(mktemp)"; list="$(mktemp)"
LC_ALL=C find "$dir" -type f \
  ! -name 'capsule.receipt.json' \
  -printf '%P\n' | LC_ALL=C sort > "$list"
# leaves = sha256(filebytes)
> "$tmp"
while IFS= read -r rel; do
  sha=$(sha256sum "$dir/$rel" | awk '{print $1}')
  printf "%s  %s\n" "$sha" "$rel" >> "$tmp"
done < "$list"

# fold pairs deterministically to a single root
root=$(awk 'BEGIN{cmd=""; i=0}
{a[i++]=$1}
END{
  n=i
  if(n==0){print "0".sprintf("%063d",0); exit}
  while(n>1){
    m=0
    for(k=0;k<n;k+=2){
      if(k+1<n){
        printf "%s%s\n", a[k], a[k+1] | "sha256sum" | getline line
        close("sha256sum")
        split(line,parts," "); a2[m++]=parts[1]
      }else{
        a2[m++]=a[k]
      }
    }
    # copy back
    for(j=0;j<m;j++) a[j]=a2[j]
    n=m
  }
  print a[0]
}' "$tmp")

utc="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
family="$(basename "$dir" | cut -d- -f1)"
rec="$dir/capsule.receipt.json"
# minimal JSON, stable formatting
printf '{%s"capsule":"%s",%s"utc":"%s",%s"merkle_root":"%s"}\n' \
  $'\n  ' "$(basename "$dir")" $'\n  ' "$utc" $'\n  ' "$root" > "$rec"
echo "[CAPSEAL] merkle_root=$root"

# global index
idx=".tau_ledger/capsules.tsv"; mkdir -p "$(dirname "$idx")"
printf "%s\t%s\t%s\t%s\n" "$family" "$(basename "$dir")" "$root" "$rec" >> "$idx"
echo "[CAPSEAL] indexed $family $(basename "$dir")"
rm -f "$tmp" "$list"
