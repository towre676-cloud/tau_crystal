#!/usr/bin/env bash
# Evaluate a discrete loop holonomy: steps N over λ∈{0,..,N-1}, seed optional
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"; REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
# shellcheck source=scripts/dchar_lib.sh
source "${SCRIPT_DIR}/dchar_lib.sh"
command -v log_info  >/dev/null 2>&1 || log_info(){  printf '[INFO] %s\n'  "$*"; }
command -v log_ok    >/dev/null 2>&1 || log_ok(){    printf '[OK] %s\n'    "$*"; }
command -v log_warn  >/dev/null 2>&1 || log_warn(){  printf '[WARN] %s\n'   "$*" >&2; }
command -v log_error >/dev/null 2>&1 || log_error(){ printf '[ERROR] %s\n'  "$*" >&2; }
command -v log_fatal >/dev/null 2>&1 || log_fatal(){ log_error "$@"; exit 1; }
if [ -f "${SCRIPT_DIR}/utils.sh" ]; then source "${SCRIPT_DIR}/utils.sh"; fi

usage(){ echo "Usage: $0 [--steps N] [--seed S]"; }
STEPS=64; SEED="0"
while [ $# -gt 0 ]; do
  case "$1" in
    --steps) STEPS="${2:?}"; shift 2;;
    --seed)  SEED="${2:?}"; shift 2;;
    -h|--help) usage; exit 0;;
    *) echo "Unknown arg: $1" >&2; usage; exit 1;;
  esac
done

log_info "τ-Crystal: loop holonomy with STEPS=${STEPS}, SEED=${SEED}"
tmp_leaves="$(mktemp)"; : > "$tmp_leaves"
sum_phase="0.0"
i=0
while [ "$i" -lt "$STEPS" ]; do
  # λ = i / STEPS as rational string; keep both i and N to avoid float drift in serialization
  lam_num="$i"; lam_den="$STEPS"
  payload="$(tau_serialize "v=1" "loop=unit" "i=${lam_num}" "n=${lam_den}" "seed=${SEED}" "site=τ-crystal")"
  h="$(tau_sha256_str "$payload")"
  printf "%s\n" "$h" >> "$tmp_leaves"
  ph="$(tau_phase64 "$h")"
  sum_phase="$(awk -v a="$sum_phase" -v b="$ph" 'BEGIN{ s=a+b; while(s>=1.0) s-=1.0; while(s<0.0) s+=1.0; printf("%.17f\n", s); }')"
  i=$((i+1))
done
root="$(tau_merkle_root "$tmp_leaves")"
rm -f "$tmp_leaves"
rec_dir="$(tau_receipt_dir)"
rec_file="${rec_dir}/loop.receipt"
: > "$rec_file"
printf "%s\n" "kind=loop"            >> "$rec_file"
printf "%s\n" "steps=${STEPS}"        >> "$rec_file"
printf "%s\n" "seed=${SEED}"          >> "$rec_file"
printf "%s\n" "phase_frac=${sum_phase}" >> "$rec_file"
printf "%s\n" "root_sha256=${root}"   >> "$rec_file"
log_ok "Holonomy (phase fraction in [0,1)): ${sum_phase}"
log_ok "Merkle root: ${root}"
log_ok "Receipt: ${rec_file}"
