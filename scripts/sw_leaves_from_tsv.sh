#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/dchar_lib.sh"
[ -f "${SCRIPT_DIR}/utils.sh" ] && source "${SCRIPT_DIR}/utils.sh" || true
FILE="${1:?Usage: sw_leaves_from_tsv.sh <A.tsv> [seed_default] }"
SEED_DEFAULT="${2:-swpf0}"
tmp_hash="$(mktemp)"; tmp_pairs="$(mktemp)"
sed -i "s/\r$//" "$FILE" 2>/dev/null || true
awk -v OFS="\t" 'NR==1{next} {print $1,$2,$3,$4,$5,$6,$7,(NF>=8?$8:"")}' "$FILE" | while IFS=$'\t' read -r u a a1 a2 p2 p1 p0 sd; do
  [ -z "${sd}" ] && sd="$SEED_DEFAULT"
  pl="$(tau_serialize "v=1" "chart=sw_pf" "u=${u}" "a=${a}" "a1=${a1}" "a2=${a2}" "p2=${p2}" "p1=${p1}" "p0=${p0}" "seed=${sd}")"
  h="$(tau_sha256_str "$pl")"
  printf "%s\n" "$h" >> "$tmp_hash"
  printf "%s\t%s\n" "$u" "$h" >> "$tmp_pairs"
done
root="$(tau_merkle_root "$tmp_hash")"; rm -f "$tmp_hash"
dir="$(tau_receipt_dir)"; leaves="${dir}/sw_pf.leaves.txt"; mv "$tmp_pairs" "$leaves"
printf "ROOT\t%s\nLEAVES\t%s\n" "$root" "$leaves"
