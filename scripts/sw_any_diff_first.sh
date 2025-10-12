#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ -f "${SCRIPT_DIR}/utils.sh" ] && source "${SCRIPT_DIR}/utils.sh" || {
  log_ok(){ printf "[OK] %s\n" "$*"; }; log_error(){ printf "[ERROR] %s\n" "$*" >&2; }
}
A="${1:?Usage: sw_any_diff_first.sh <A.tsv> <B.tsv> [seed_def] }"
B="${2:?}"; SD="${3:-swpf0}"
sed -i 's/\r$//' "$A" "$B" 2>/dev/null || true
OA="$(bash "${SCRIPT_DIR}/sw_any_feed.sh" "$A" A "$SD" 2>/dev/null | tr -d '\r')"
OB="$(bash "${SCRIPT_DIR}/sw_any_feed.sh" "$B" B "$SD" 2>/dev/null | tr -d '\r')"
LA="$(printf "%s\n" "$OA" | sed -n 's/^LEAVES[[:space:]]\+//p' | tail -1)"
LB="$(printf "%s\n" "$OB" | sed -n 's/^LEAVES[[:space:]]\+//p' | tail -1)"
[ -r "$LA" ] || { log_error "no leaves from A"; exit 2; }
[ -r "$LB" ] || { log_error "no leaves from B"; exit 2; }
as="$(mktemp)"; bs="$(mktemp)"
sort -t$'\t' -k1,1 "$LA" > "$as"
sort -t$'\t' -k1,1 "$LB" > "$bs"
join -a1 -a2 -t$'\t' -e "" -o 0,1.2,2.2 "$as" "$bs" | \
while IFS=$'\t' read -r u ha hb; do
  if [ -z "${ha:-}" ] || [ -z "${hb:-}" ] || [ "$ha" != "$hb" ]; then
    printf "[DIFF] u=%s\n[A] %s\n[B] %s\n" "$u" "${ha:-<missing>}" "${hb:-<missing>}"
    rm -f "$as" "$bs"; exit 1
  fi
done
rm -f "$as" "$bs"
echo "[OK] No differences."
