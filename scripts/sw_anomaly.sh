#!/usr/bin/env bash
# Usage: sw_anomaly.sh <base.tsv> <colname> <eps_rel> [decimals]
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Logs shim if utils.sh not present in subshells
if [ -f "${SCRIPT_DIR}/utils.sh" ]; then
  . "${SCRIPT_DIR}/utils.sh"
else
  log_ok(){ printf "[OK] %s\n" "$*"; }
  log_error(){ printf "[ERROR] %s\n" "$*" >&2; }
fi

A="${1:?}"; COL="${2:?}"; EPS="${3:?}"; DEC="${4:-}"
sed -i 's/\r$//' "$A"

A_Q="$(mktemp)"; B="$(mktemp)"; B_Q="$(mktemp)"
bash "${SCRIPT_DIR}/tsv_perturb.sh" "$A" "$COL" "$EPS" "$B"

if [ -n "$DEC" ]; then
  bash "${SCRIPT_DIR}/tsv_quantize.sh" "$A" "$DEC" "$A_Q"
  bash "${SCRIPT_DIR}/tsv_quantize.sh" "$B" "$DEC" "$B_Q"
  A_USE="$A_Q"; B_USE="$B_Q"
else
  A_USE="$A";  B_USE="$B"
fi

set +e
bash "${SCRIPT_DIR}/sw_certify.sh" "$A_USE" "$B_USE" A B swpf0
RC=$?
set -e

if [ $RC -eq 0 ]; then
  log_ok "Certified equal (DEC=${DEC:-none})."
else
  log_error "Mismatch detected (DEC=${DEC:-none})."
fi

rm -f "$A_Q" "$B" "$B_Q" 2>/dev/null || true
