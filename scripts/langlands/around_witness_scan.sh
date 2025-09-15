#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
best="analysis/reciprocity_best.env"; sec="analysis/reciprocity_second.env"
readv(){ f="$1"; k="$2"; awk -F= -v k="$k" '$1==k{gsub(/\r/,"",$2);print $2}' "$f" 2>/dev/null | head -n1; }
S1="$(readv "$best" BEST_S_MICRO)"; T1="$(readv "$best" BEST_T_MICRO)"; S2="$(readv "$sec" BEST_S_MICRO)"; T2="$(readv "$sec" BEST_T_MICRO)"
[ -n "$S1" ] || { echo "[atlas] skip: need BEST_* in analysis/reciprocity_best.env"; exit 0; }
: "${S2:=$S1}"; : "${T2:=$T1}"
padS="${S_PAD:-50000}"; padT="${T_PAD:-50000}"; stepS="${S_STEP:-2000}"; stepT="${T_STEP:-2000}"
min(){ a="$1"; b="$2"; [ "$a" -lt "$b" ] && echo "$a" || echo "$b"; }
max(){ a="$1"; b="$2"; [ "$a" -gt "$b" ] && echo "$a" || echo "$b"; }
export S_MIN=$(( $(min "$S1" "$S2") - padS )) S_MAX=$(( $(max "$S1" "$S2") + padS ))
export T_MIN=$(( $(min "$T1" "$T2") - padT )) T_MAX=$(( $(max "$T1" "$T2") + padT ))
export S_STEP="$stepS" T_STEP="$stepT"
OUT="analysis/bash_theta_scan.tsv"; echo "[atlas] scanning S=[${S_MIN},${S_MAX}] T=[${T_MIN},${T_MAX}] step=(${S_STEP},${T_STEP})"
rows_before=$([ -f "$OUT" ] && wc -l < "$OUT" 2>/dev/null || echo 0)
if [ -x scripts/langlands/theta_scan_wide.sh ]; then bash scripts/langlands/theta_scan_wide.sh .tau_ledger .tau_ledger/demo || true; fi
rows=$([ -f "$OUT" ] && wc -l < "$OUT" 2>/dev/null || echo 0)
[ "$rows" -le 1 ] && bash scripts/langlands/theta_scan_proxy.sh
rows_after=$([ -f "$OUT" ] && wc -l < "$OUT" 2>/dev/null || echo 0)
echo "[atlas] wrote $OUT (rows before=$rows_before after=$rows_after)"
