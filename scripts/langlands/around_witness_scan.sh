#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
best="analysis/reciprocity_best.env"; sec="analysis/reciprocity_second.env"
[ -s "$best" ] || best=""
[ -s "$sec" ]  || sec=""
[ -x scripts/langlands/theta_scan_wide.sh ] || { echo "[atlas] skip: theta_scan_wide.sh missing"; exit 0; }
readv(){ f="$1"; k="$2"; awk -F= -v k="$k" '$1==k{gsub(/\r/,"",$2);print $2}' "$f" 2>/dev/null | head -n1; }
S1=$(readv "$best" BEST_S_MICRO); T1=$(readv "$best" BEST_T_MICRO)
S2=$(readv "$sec"  BEST_S_MICRO); T2=$(readv "$sec"  BEST_T_MICRO)
[ -n "$S1" ] || { echo "[atlas] skip: no reciprocity envs"; exit 0; }
[ -n "$S2" ] || { S2="$S1"; T2="$T1"; }
padS=${S_PAD:-50000}; padT=${T_PAD:-50000}; stepS=${S_STEP:-2000}; stepT=${T_STEP:-2000}
min(){ a="$1"; b="$2"; [ "$a" -lt "$b" ] && echo "$a" || echo "$b"; }
max(){ a="$1"; b="$2"; [ "$a" -gt "$b" ] && echo "$a" || echo "$b"; }
Slo=$(( $(min "$S1" "$S2") - padS )); Shi=$(( $(max "$S1" "$S2") + padS ))
Tlo=$(( $(min "$T1" "$T2") - padT )); Thi=$(( $(max "$T1" "$T2") + padT ))
export S_MIN="$Slo" S_MAX="$Shi" S_STEP="$stepS" T_MIN="$Tlo" T_MAX="$Thi" T_STEP="$stepT"
echo "[atlas] scanning S=[${S_MIN},${S_MAX}] T=[${T_MIN},${T_MAX}] step=(${S_STEP},${T_STEP})"
bash scripts/langlands/theta_scan_wide.sh .tau_ledger .tau_ledger/demo || true
echo "[atlas] wrote analysis/bash_theta_scan.tsv"

# fallback if theta_scan_wide.sh missing or fails
[ -x scripts/langlands/theta_scan_wide.sh ] && bash scripts/langlands/theta_scan_wide.sh .tau_ledger .tau_ledger/demo || bash scripts/langlands/theta_scan_proxy.sh
