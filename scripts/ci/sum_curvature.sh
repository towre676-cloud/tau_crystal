#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then ROOT="$(git rev-parse --show-toplevel 2>/dev/null || printf "%s" "$PWD")"; else ROOT="${ROOT_OVERRIDE:-$HOME/Desktop/tau_crystal/tau_crystal}"; fi
cd "$ROOT" || { echo "[error] could not cd to ROOT=$ROOT" >&2; exit 2; }
TARGET="${1:-}"; if [ -z "$TARGET" ]; then TARGET="$(ls -1t .tau_ledger/*/*/curvature/*.tsv 2>/dev/null | head -n 1 || true)"; fi
if [ -z "${TARGET:-}" ] || [ ! -f "$TARGET" ]; then echo "usage: scripts/ci/sum_curvature.sh [FILE.tsv]  (no arg = latest under $ROOT/.tau_ledger)"; exit 1; fi
echo "[info] ROOT=$ROOT"; echo "[info] FILE=$TARGET"
awk -F"\t" '{ if(NR==1){next} c++; for(i=1;i<=NF;i++){s[i]+=$i; ss[i]+=$i*$i} } END { if(c==0){print "rows=0"; exit 0} printf "rows=%d\n", c; for(i=1;i<=NF;i++){ m=s[i]/c; v=(ss[i]/c - m*m); if(v<0) v=0; printf "col[%d]_sum=%s\ncol[%d]_mean=%s\ncol[%d]_std=%s\n", i, s[i], i, m, i, sqrt(v) } }' "$TARGET"
