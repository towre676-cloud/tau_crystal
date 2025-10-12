#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ -f "${SCRIPT_DIR}/dchar_lib.sh" ] && source "${SCRIPT_DIR}/dchar_lib.sh" || true
[ -f "${SCRIPT_DIR}/utils.sh" ] && source "${SCRIPT_DIR}/utils.sh" || true
A="${1:?Usage: sw_diff_first.sh <A.tsv> <B.tsv> [seed_default] }"
B="${2:?}"; SEED="${3:-swpf0}"
sed -i "s/\r$//" "$A" "$B" 2>/dev/null || true
outA="$(bash "${SCRIPT_DIR}/sw_leaves_from_tsv.sh" "$A" "$SEED" 2>/dev/null || true)"
outB="$(bash "${SCRIPT_DIR}/sw_leaves_from_tsv.sh" "$B" "$SEED" 2>/dev/null || true)"
LA="$(printf "%s\n" "$outA" | sed -n "s/^LEAVES[[:space:]]\\+//p" | tail -1)"
LB="$(printf "%s\n" "$outB" | sed -n "s/^LEAVES[[:space:]]\\+//p" | tail -1)"
[ -n "$LA" ] && [ -r "$LA" ] || { echo "[ERROR] no leaves from A" >&2; exit 2; }
[ -n "$LB" ] && [ -r "$LB" ] || { echo "[ERROR] no leaves from B" >&2; exit 3; }
awk -v FA="$LA" -v FB="$LB" 'BEGIN{
  n=0;
  while ((getline < FA) > 0) { u=$1; h=$2; if(u!=""){ a[u]=h; ord[++n]=u } } close(FA);
  while ((getline < FB) > 0) { u=$1; h=$2; if(u!=""){ b[u]=h } } close(FB);
  for (i=1; i<=n; i++) {
    u=ord[i]; if (!(u in b)) { printf("[DIFF] missing in B: u=%s\n", u); exit 1 }
    if (a[u] != b[u]) { printf("[DIFF] u=%s\nA=%s\nB=%s\n", u, a[u], b[u]); exit 1 }
  }
  for (u in b) { if (!(u in a)) { printf("[DIFF] extra in B: u=%s\n", u); exit 1 } }
  print "[OK] No differences."; exit 0
}'  </dev/null
