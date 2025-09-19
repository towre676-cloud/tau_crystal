#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1
OUT="analysis/laurent_ring.tsv"; mkdir -p analysis
theta=$(awk -v key=theta_min -v def="" -f scripts/tools/read_kv2.awk analysis/arith_nonce.tsv 2>/dev/null || true)
seed=$(awk  -v key=gd_inv    -v def="" -f scripts/tools/read_kv2.awk analysis/arith_nonce.tsv 2>/dev/null || true)
# fallback: derive θ from passport nonce if θ is empty/NaN
if [ -z "${theta:-}" ] || [ "$theta" = "NaN" ]; then
  nhex=$(awk -v key=nonce_hex -v def="" -f scripts/tools/read_kv2.awk analysis/passport_sig.tsv 2>/dev/null || true)
  [ -z "$nhex" ] && nhex=$(grep -o "\"nonce\":\"[0-9a-fA-F]\\{16,64\\}\"" -m1 analysis/fused_gates.json 2>/dev/null | sed 's/.*"nonce":"//; s/".*//' ) || true
  if [ -n "$nhex" ]; then
    int=$(( 16#${nhex:0:8} ))
    theta=$(awk -v i="$int" 'BEGIN{pi=4*atan2(1,1); t=(i%10000000)/10000000.0; if(t<=0)t=1e-9; if(t>=1)t=1-1e-9; printf "%.17g", t*pi}')
  fi
fi
[ -f "$OUT" ] || printf "Re(L)\tIm(L)\tK_k\tq\tnonce_seed\n" > "$OUT"
if [ -z "${theta:-}" ] || [ "$theta" = "NaN" ]; then printf "NaN\tNaN\tNaN\tNaN\t%s\n" "${seed:-}" >> "$OUT"; exit 2; fi
awk -v theta="$theta" -v seed="${seed:-}" -f scripts/laurent/laurent_eval.awk >> "$OUT"
exit 0
