#!/usr/bin/env bash
# PF feeder: TSV(u a a1 a2 p2 p1 p0 [seed]) -> residuals, Merkle receipt
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/dchar_lib.sh"
[ -f "${SCRIPT_DIR}/utils.sh" ] && { unset TAU_UTILS_LOADED; source "${SCRIPT_DIR}/utils.sh"; } || true
type log_info  >/dev/null 2>&1 || log_info(){  printf "[INFO] %s\n"  "$*"; }
type log_ok    >/dev/null 2>&1 || log_ok(){    printf "[OK] %s\n"    "$*"; }
type log_error >/dev/null 2>&1 || log_error(){ printf "[ERROR] %s\n" "$*" >&2; }

FILE="${1:?Usage: sw_pf_feed.sh <tsv> [method-tag] [seed-default] }"
METHOD="${2:-methodA}"
SEED_DEFAULT="${3:-swpf0}"

tmp="$(mktemp)"; : > "$tmp"
phase="0.0"; rows=0; l1="0.0"; rmax="0.0"; umax=""

# Open file on FD 3; skip header once; read rows on same shell (no pipeline subshell)
exec 3<"$FILE"
IFS=$'\t' read -r _hdr1 _hdr2 _hdr3 _hdr4 _hdr5 _hdr6 _hdr7 _hdr8 <&3 || true
while IFS=$'\t' read -r u a a1 a2 p2 p1 p0 sd <&3; do
  [ -z "${u-}" ] && continue
  [ -z "${sd-}" ] && sd="$SEED_DEFAULT"
  r="$(awk -v a="$a" -v a1="$a1" -v a2="$a2" -v p2="$p2" -v p1="$p1" -v p0="$p0" 'BEGIN{printf("%.17g\n", p2*a2 + p1*a1 + p0*a)}')"
  ar="$(awk -v x="$r" 'BEGIN{if(x<0)x=-x; printf("%.17g\n",x)}')"
  # IMPORTANT: do NOT include METHOD in hashed payload; store it only in receipt metadata.
  pl="$(tau_serialize "v=1" "chart=sw_pf" "u=${u}" "a=${a}" "a1=${a1}" "a2=${a2}" "p2=${p2}" "p1=${p1}" "p0=${p0}" "residual=${r}" "seed=${sd}")"
  h="$(tau_sha256_str "$pl")"; printf "%s\n" "$h" >> "$tmp"
  ph="$(tau_phase64 "$h")"; phase="$(awk -v a="$phase" -v b="$ph" 'BEGIN{s=a+b; while(s>=1)s-=1; printf("%.17f\n",s)}')"
  rows=$((rows+1))
  l1="$(awk -v L="$l1" -v x="$ar" 'BEGIN{printf("%.17g\n", L+x)}')"
  if awk -v x="$ar" -v m="$rmax" 'BEGIN{exit !(x>m)}'; then rmax="$ar"; umax="$u"; fi
done
exec 3<&-

root="$(tau_merkle_root "$tmp")"; rm -f "$tmp"
dir="$(tau_receipt_dir)"; rec="${dir}/sw_pf_${METHOD}.receipt"; : > "$rec"
printf "%s\n" "kind=sw_pf"            >> "$rec"
printf "%s\n" "file=${FILE}"          >> "$rec"
printf "%s\n" "method=${METHOD}"      >> "$rec"
printf "%s\n" "rows=${rows}"          >> "$rec"
printf "%s\n" "phase_frac=${phase}"   >> "$rec"
printf "%s\n" "res_L1=${l1}"          >> "$rec"
printf "%s\n" "res_Linf=${rmax}"      >> "$rec"
printf "%s\n" "res_u_at_max=${umax}"  >> "$rec"
printf "%s\n" "root_sha256=${root}"   >> "$rec"

log_ok "SW PF root (${METHOD}): ${root}"
log_ok "Residuals: L1=${l1}, Linf=${rmax} @ u=${umax} (rows=${rows})"
log_ok "Receipt: ${rec}"
printf "ROOT\t%s\n" "$root"
printf "RECEIPT\t%s\n" "$rec"
