#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ -f "${SCRIPT_DIR}/utils.sh" ] && source "${SCRIPT_DIR}/utils.sh" || {
  log_ok(){ printf "[OK] %s\n" "$*"; }; log_error(){ printf "[ERROR] %s\n" "$*" >&2; }
}
A="${1:?Usage: sw_any_certify.sh <A.tsv> <B.tsv> <tagA> <tagB> [seed_def] }"
B="${2:?}"; TA="${3:?}"; TB="${4:?}"; SD="${5:-swpf0}"
sed -i 's/\r$//' "$A" "$B" 2>/dev/null || true
OA="$(bash "${SCRIPT_DIR}/sw_any_feed.sh" "$A" "$TA" "$SD" 2>/dev/null | tr -d '\r')"
OB="$(bash "${SCRIPT_DIR}/sw_any_feed.sh" "$B" "$TB" "$SD" 2>/dev/null | tr -d '\r')"
RA="$(printf "%s\n" "$OA" | sed -n 's/^ROOT[[:space:]]\+//p' | tail -1)"
RB="$(printf "%s\n" "$OB" | sed -n 's/^ROOT[[:space:]]\+//p' | tail -1)"
printf "[INFO] root(%s) = %s\n" "$TA" "$RA"
printf "[INFO] root(%s) = %s\n" "$TB" "$RB"
if [ "$RA" = "$RB" ]; then echo "[OK] Certified: roots match."; exit 0; else
  echo "[ERROR] Roots differ." >&2; exit 1; fi
