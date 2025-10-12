#!/usr/bin/env bash
# Ingest TSV (tau_re tau_im z_re z_im [seed]) → Merkle receipt
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"; source "${SCRIPT_DIR}/dchar_lib.sh"
[ -f "${SCRIPT_DIR}/utils.sh" ] && source "${SCRIPT_DIR}/utils.sh" || true
FILE="${1:?Usage: dchar_feed.sh <tsv-file> [seed-default]}"; SEED_DEFAULT="${2:-feed0}"
tmp="$(mktemp)"; : > "$tmp"; phase="0.0"
awk -v OFS="\t" 'NR==1{next} {sd=(NF>=5?$5:""); print $1,$2,$3,$4,sd}' "$FILE" |
while IFS=$'\t' read -r tr ti zr zi sd; do
  [ -z "${sd}" ] && sd="$SEED_DEFAULT"
  pl="$(tau_serialize "v=1" "chart=feed" "tau_re=${tr}" "tau_im=${ti}" "z_re=${zr}" "z_im=${zi}" "seed=${sd}")"
  h="$(tau_sha256_str "$pl")"; printf "%s\n" "$h" >> "$tmp"
  ph="$(tau_phase64 "$h")"; phase="$(awk -v a="$phase" -v b="$ph" 'BEGIN{s=a+b; while(s>=1)s-=1; printf("%.17f\n",s)}')"
done
root="$(tau_merkle_root "$tmp")"; rm -f "$tmp"
dir="$(tau_receipt_dir)"; rec="${dir}/feed.receipt"; : > "$rec"
printf "%s\n" "kind=feed"           >> "$rec"
printf "%s\n" "file=${FILE}"        >> "$rec"
printf "%s\n" "phase_frac=${phase}" >> "$rec"
printf "%s\n" "root_sha256=${root}" >> "$rec"
log_ok "Feed root: ${root}"
log_ok "Receipt: ${rec}"
