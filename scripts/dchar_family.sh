#!/usr/bin/env bash
# Evaluate a finite grid family F = { (τ_i, z_j) } and emit a coherent Merkle root
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"; REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
source "${SCRIPT_DIR}/dchar_lib.sh"
command -v log_info  >/dev/null 2>&1 || log_info(){  printf '[INFO] %s\n'  "$*"; }
command -v log_ok    >/dev/null 2>&1 || log_ok(){    printf '[OK] %s\n'    "$*"; }
command -v log_warn  >/dev/null 2>&1 || log_warn(){  printf '[WARN] %s\n'   "$*" >&2; }
command -v log_error >/dev/null 2>&1 || log_error(){ printf '[ERROR] %s\n'  "$*" >&2; }
command -v log_fatal >/dev/null 2>&1 || log_fatal(){ log_error "$@"; exit 1; }
if [ -f "${SCRIPT_DIR}/utils.sh" ]; then source "${SCRIPT_DIR}/utils.sh"; fi

TAU_POINTS=("i/5" "2i/5" "i/2" "3i/5" "4i/5")
Z_POINTS=("0" "1/6" "1/3" "1/2")
SEED="${1:-family0}"
log_info "τ-Crystal: family evaluation over |TAU|="${#TAU_POINTS[@]}" × |Z|="${#Z_POINTS[@]}" with SEED=${SEED}"
tmp_leaves="$(mktemp)"; : > "$tmp_leaves"
for t in "${TAU_POINTS[@]}"; do
  for z in "${Z_POINTS[@]}"; do
    payload="$(tau_serialize "v=1" "chart=jacobi" "tau=${t}" "z=${z}" "seed=${SEED}")"
    printf "%s\n" "$(tau_sha256_str "$payload")" >> "$tmp_leaves"
  done
done
root="$(tau_merkle_root "$tmp_leaves")"; rm -f "$tmp_leaves"
rec_dir="$(tau_receipt_dir)"; rec_file="${rec_dir}/family.receipt"; : > "$rec_file"
printf "%s\n" "kind=family"        >> "$rec_file"
printf "%s\n" "tau_points=${#TAU_POINTS[@]}" >> "$rec_file"
printf "%s\n" "z_points=${#Z_POINTS[@]}"   >> "$rec_file"
printf "%s\n" "seed=${SEED}"       >> "$rec_file"
printf "%s\n" "root_sha256=${root}" >> "$rec_file"
log_ok "Family Merkle root: ${root}"
log_ok "Receipt: ${rec_file}"
