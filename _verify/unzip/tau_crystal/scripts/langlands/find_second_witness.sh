#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
TOL="${1:-0}"
S_EXCL_U="${S_EXCL_U:-30000}"
T_EXCL_U="${T_EXCL_U:-30000}"
SCAN="analysis/bash_theta_scan.tsv"
[ -f analysis/reciprocity_best.env ] || { echo "[err] missing analysis/reciprocity_best.env"; exit 2; }
. analysis/reciprocity_best.env 2>/dev/null || true
BEST_S_MICRO="${BEST_S_MICRO:-294000}"
BEST_T_MICRO="${BEST_T_MICRO:--176000}"
[ -s "$SCAN" ] || { echo "[err] missing $SCAN"; exit 2; }
best=$(awk -v s0="$BEST_S_MICRO" -v t0="$BEST_T_MICRO" -v sx="$S_EXCL_U" -v tx="$T_EXCL_U" -v tol="$TOL" 'BEGIN{best=-1} $0 ~ /^#/ {next} {s=$2; t=$3; if(s==""||t=="")next; if((s>=s0-sx && s<=s0+sx) && (t>=t0-tx && t<=t0+tx))next; r2=s*s+t*t; if(tol>0 && r2>tol*tol)next; if(best<0 || r2<best){best=r2; bs=s; bt=t}} END{if(best<0)exit 1; printf("%d %d\n", bs, bt)}' "$SCAN") || { echo "[err] no second witness found (adjust TOL/exclusion or scan)"; exit 3; }
S2="${best% *}"; T2="${best#* }"
: > analysis/reciprocity_second.env
printf "SECOND_S_MICRO=%s\n" "$S2" >> analysis/reciprocity_second.env
printf "SECOND_T_MICRO=%s\n" "$T2" >> analysis/reciprocity_second.env
printf "second_witness: S=%s  T=%s\n" "$S2" "$T2" | tee analysis/reciprocity_second.txt
