#!/usr/bin/env bash
set -euo pipefail; umask 022
source scripts/capsule/merkle_lib.sh

caps_dir="analysis/capsules"; mkdir -p "$caps_dir" .tau_ledger

arg1="${1:-auto}"
arg2="${2:-}"

if [[ "$arg1" == */* ]]; then
  # directory mode: arg1 is a capsule dir path
  capsule="$(realpath -m "$arg1")"
  family="$(basename "$capsule" | sed 's/-[0-9TZ]*$//')"
  capsule_basename="$(basename "$capsule")"
else
  # family mode
  family="$arg1"
  if [ -n "$arg2" ]; then
    capsule_basename="$arg2"
  else
    ts="$(date -u +%Y%m%dT%H%M%SZ)"
    capsule_basename="${family}-${ts}"
  fi
  capsule="$caps_dir/$capsule_basename"
fi

mkdir -p "$capsule"

btxt="$capsule/boundary.txt"
bsig="$capsule/boundary.sig"
if [ ! -f "$btxt" ]; then
  {
    printf "Capsule: %s\n" "$capsule_basename"
    printf "Family:  %s\n" "$family"
    printf "UTC:     %s\n" "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    printf "Policy:  contents exclude capsule.receipt.json\n"
  } > "$btxt"
fi
sha256sum "$btxt" | awk '{print $1}' > "$bsig"

root="$(merkle__dir_root "$capsule")"
utc="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
printf '{\n  "capsule":"%s",\n  "utc":"%s",\n  "merkle_root":"%s"\n}\n' "$capsule_basename" "$utc" "$root" > "$capsule/capsule.receipt.json"

idx=".tau_ledger/capsules.tsv"
: > "${idx}.tmp.$$"
awk -v OFS='\t' -v f="$family" -v c="$capsule_basename" '!(NF && $1==f && $2==c){print $0}' "$idx" 2>/dev/null | sed '/^$/d' >> "${idx}.tmp.$$"
printf "%s\t%s\t%s\t%s/capsule.receipt.json\n" "$family" "$capsule_basename" "$root" "$capsule" >> "${idx}.tmp.$$"
mv "${idx}.tmp.$$" "$idx"

echo "merkle_root=$root"
echo "[CAPSEAL] indexed $family $capsule_basename"
echo "[CAP] wrote $capsule"
