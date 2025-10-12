#!/usr/bin/env bash
# Certify two PF datasets: compare Merkle roots of receipts (robust parse)
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/dchar_lib.sh"
[ -f "${SCRIPT_DIR}/utils.sh" ] && { unset TAU_UTILS_LOADED; source "${SCRIPT_DIR}/utils.sh"; } || true
type log_info  >/dev/null 2>&1 || log_info(){  printf "[INFO] %s\n"  "$*"; }
type log_ok    >/dev/null 2>&1 || log_ok(){    printf "[OK] %s\n"    "$*"; }
type log_error >/dev/null 2>&1 || log_error(){ printf "[ERROR] %s\n" "$*" >&2; }
A="${1:?Usage: sw_certify.sh <tsvA> <tsvB> [tagA] [tagB] [seed-default] }"
B="${2:?}"
TA="${3:-A}"
TB="${4:-B}"
SEED_DEFAULT="${5:-swpf0}"
extract_root(){ printf "%s\n" "$1" | tr -d "\r" | sed -n 's/^ROOT[[:space:]]\+//p' | tail -1; }
fallback_root(){ printf "%s\n" "$1" | tr -d "\r" | sed -n 's/.*root_sha256=\([a-f0-9]\{64\}\).*/\1/p' | tail -1; }
OUTA="$(bash "${SCRIPT_DIR}/sw_pf_feed.sh" "$A" "$TA" "$SEED_DEFAULT")"
OUTB="$(bash "${SCRIPT_DIR}/sw_pf_feed.sh" "$B" "$TB" "$SEED_DEFAULT")"
RA="$(extract_root "$OUTA")"; [ -n "$RA" ] || RA="$(fallback_root "$OUTA")"
RB="$(extract_root "$OUTB")"; [ -n "$RB" ] || RB="$(fallback_root "$OUTB")"
printf "[INFO] root(%s) = %s\n" "$TA" "$RA"
printf "[INFO] root(%s) = %s\n" "$TB" "$RB"
if [ "$RA" = "$RB" ]; then echo "[OK] Certified: roots match."; exit 0; else echo "[ERROR] Roots differ."; exit 1; fi
