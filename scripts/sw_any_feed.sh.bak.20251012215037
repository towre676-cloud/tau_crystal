#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# core libs
source "${SCRIPT_DIR}/dchar_lib.sh"
[ -f "${SCRIPT_DIR}/utils.sh" ] && source "${SCRIPT_DIR}/utils.sh" || {
  log_ok(){ printf "[OK] %s\n" "$*"; }; log_error(){ printf "[ERROR] %s\n" "$*" >&2; }
}
FILE="${1:?Usage: sw_any_feed.sh <tsv> <tag> [seed_default] }"
TAG="${2:?}"; SEED_DEFAULT="${3:-swpf0}"
sed -i 's/\r$//' "$FILE" 2>/dev/null || true

canon(){ printf "%s" "$1" | tr 'A-Z' 'a-z' | sed -E 's/[^a-z0-9_]+/_/g; s/^_+//; s/_+$//; s/__+/_/g'; }

tmp_hash="$(mktemp)"; : > "$tmp_hash"
tmp_leaves="$(mktemp)"; : > "$tmp_leaves"
phase="0.0"; rows=0

# header -> KEYS[]
IFS=$'\t' read -r -a HDR < "$FILE" || { log_error "empty TSV: $FILE"; exit 2; }
declare -a KEYS=()
for h in "${HDR[@]}"; do KEYS+=( "$(canon "$h")" ); done

seed_idx=-1; u_idx=-1
for i in "${!KEYS[@]}"; do
  [ "${KEYS[$i]}" = "seed" ] && seed_idx=$i
  [ "${KEYS[$i]}" = "u" ] && u_idx=$i
done

tail -n +2 "$FILE" | while IFS=$'\t' read -r -a ROW || [ -n "${ROW[*]:-}" ]; do
  [ "${#ROW[@]}" -eq 0 ] && continue
  rows=$((rows+1))
  seed_val="$SEED_DEFAULT"
  if [ $seed_idx -ge 0 ]; then
    seed_val="${ROW[$seed_idx]:-}"
    [ -z "$seed_val" ] && seed_val="$SEED_DEFAULT"
  fi
  declare -a KV=( "v=1" "chart=sw_any" "seed=${seed_val}" )
  for j in "${!KEYS[@]}"; do
    k="${KEYS[$j]}"; v="${ROW[$j]:-}"
    [ "$k" = "seed" ] && v="$seed_val"
    KV+=( "$k=$v" )
  done
  payload="$(tau_serialize "${KV[@]}")"
  h="$(tau_sha256_str "$payload")"; printf "%s\n" "$h" >> "$tmp_hash"
  ph="$(tau_phase64 "$h")"
  phase="$(awk -v a="$phase" -v b="$ph" 'BEGIN{s=a+b; while(s>=1)s-=1; printf("%.17f\n",s)}')"
  uout="$rows"; [ $u_idx -ge 0 ] && uout="${ROW[$u_idx]}"
  printf "%s\t%s\n" "$uout" "$h" >> "$tmp_leaves"
done

root="$(tau_merkle_root "$tmp_hash")"
dir="$(tau_receipt_dir)"
safe_tag="$(printf "%s" "$TAG" | sed -E 's/[^A-Za-z0-9_.-]+/_/g')"
leaves="$dir/sw_any_${safe_tag}.leaves.txt"; mv "$tmp_leaves" "$leaves"
rm -f "$tmp_hash"

rec="$dir/sw_any_${safe_tag}.receipt"; : > "$rec"
printf "%s\n" "kind=sw_any"          >> "$rec"
printf "%s\n" "file=${FILE}"         >> "$rec"
printf "%s\n" "tag=${TAG}"           >> "$rec"
printf "%s\n" "rows=${rows}"         >> "$rec"
printf "%s\n" "phase_frac=${phase}"  >> "$rec"
printf "%s\n" "root_sha256=${root}"  >> "$rec"
printf "%s\n" "leaves_path=${leaves}" >> "$rec"

log_ok "SW ANY root (${TAG}): ${root}"
log_ok "Receipt: ${rec}"
printf "ROOT\t%s\nLEAVES\t%s\nRECEIPT\t%s\n" "$root" "$leaves" "$rec"
