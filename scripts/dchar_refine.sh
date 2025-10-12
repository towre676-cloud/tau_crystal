#!/usr/bin/env bash
# Step refinement: run multiple N and show ~O(1/N) phase convergence (robust)
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/dchar_lib.sh"
[ -f "${SCRIPT_DIR}/utils.sh" ] && source "${SCRIPT_DIR}/utils.sh" || true
SEED="${1:-0}"
NS="${2:-8,16,32,64,128}"
IFS=, read -r -a arr <<< "$NS"
latest_loop_receipt(){ ls -1dt .tau_ledger/dchar/*/loop.receipt 2>/dev/null | head -1 || true; }
parse_receipt_path(){ awk '/^Receipt: /{p=$2} END{if(p!="")print p}'; }
read_phase(){ awk -F"=" '/^phase_frac=/{print $2; exit}' "$1" 2>/dev/null || true; }
printf "N\tphase\tdphase\tN*abs(d)\n"
prev=""
for N in "${arr[@]}"; do
  OUT="(bash "${TAU_LOOP_BIN:-/dchar_loop.sh}" --steps "$N" --seed "$SEED")"
  REC="$(printf "%s\n" "$OUT" | parse_receipt_path || true)"
  [ -n "$REC" ] || REC="$(latest_loop_receipt)"
  [ -n "$REC" ] || { echo "[ERROR] No receipt found for N=$N" >&2; exit 1; }
  PH="$(read_phase "$REC")"
  [ -n "$PH" ] || { echo "[ERROR] Missing phase_frac in $REC" >&2; exit 1; }
  if [ -n "$prev" ]; then
    d="$(awk -v a="$PH" -v b="$prev" 'BEGIN{d=a-b; while(d>0.5)d-=1; while(d<-0.5)d+=1; if(d<0)d=-d; printf("%.17f\n",d)}')"
    nd="$(awk -v n="$N" -v d="$d"   'BEGIN{printf("%.9f\n", n*d)}')"
    printf "%s\t%s\t%s\t%s\n" "$N" "$PH" "$d" "$nd"
  else
    printf "%s\t%s\t-\t-\n" "$N" "$PH"
  fi
  prev="$PH"
done
