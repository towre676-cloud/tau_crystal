#!/usr/bin/env bash
# Naturality check: TTY vs piped runs must produce identical root+phase.
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"; REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
source "${SCRIPT_DIR}/dchar_lib.sh"
[ -f "${SCRIPT_DIR}/utils.sh" ] && source "${SCRIPT_DIR}/utils.sh" || true
STEPS="${1:-64}"; SEED="${2:-0}"
strip_ansi(){ sed -r "s/\x1B\[[0-9;]*[A-Za-z]//g"; }
latest_loop(){ ls -1dt .tau_ledger/dchar/*/loop.receipt 2>/dev/null | head -1 || true; }
read_root(){ grep "^root_sha256=" "$1" 2>/dev/null | cut -d"=" -f2 || true; }
read_phase(){ grep "^phase_frac="  "$1" 2>/dev/null | cut -d"=" -f2 || true; }
list_receipts(){ ls -1 .tau_ledger/dchar/*/loop.receipt 2>/dev/null || true; }
one_run(){
  local mode="$1" r_before r_after out rec
  r_before="$(list_receipts)"
  if [ "$mode" = "tty" ]; then
    bash "${SCRIPT_DIR}/dchar_loop.sh" --steps "${STEPS}" --seed "${SEED}" >/dev/null
  else
    out="$("${SCRIPT_DIR}/dchar_loop.sh" --steps "${STEPS}" --seed "${SEED}" 2>/dev/null | strip_ansi || true)"
    rec="$(printf "%s\n" "$out" | awk '{for(i=1;i<=NF-1;i++){if($i=="Receipt:"){print $(i+1); exit}}}' || true)"
  fi
  [ -n "${rec:-}" ] || {
    r_after="$(list_receipts)"
    rec="$(printf "%s\n%s\n" "$r_before" "$r_after" | sort | uniq -u | tail -1)"
  }
  [ -n "${rec:-}" ] || rec="$(latest_loop)"
  printf "%s\n" "$rec"
}
log_info "Naturality check with STEPS=${STEPS}, SEED=${SEED}"
R_TTY="$(one_run tty)"
[ -n "$R_TTY" ] || log_fatal "TTY run produced no receipt"
ROOT_TTY="$(read_root "$R_TTY")"; PHASE_TTY="$(read_phase "$R_TTY")"
R_PIPE="$(one_run piped)"
[ -n "$R_PIPE" ] || log_fatal "Piped run produced no receipt"
ROOT_PIPE="$(read_root "$R_PIPE")"; PHASE_PIPE="$(read_phase "$R_PIPE")"
printf "[INFO] TTY   root=%s phase=%s (%s)\n"   "$ROOT_TTY"  "$PHASE_TTY"  "$R_TTY"
printf "[INFO] piped root=%s phase=%s (%s)\n" "$ROOT_PIPE" "$PHASE_PIPE" "$R_PIPE"
if [ "$ROOT_TTY" = "$ROOT_PIPE" ] && [ "$PHASE_TTY" = "$PHASE_PIPE" ]; then
  printf "[OK] Naturality holds: roots and phases match.\n"
  exit 0
else
  printf "[ERROR] Mismatch detected.\n" >&2
  exit 1
fi
