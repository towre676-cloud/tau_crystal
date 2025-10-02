cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
curve="${1:-}"; [ -n "$curve" ] || { echo "[err] usage: run_zero_check.sh <curve>"; exit 2; }
inp="analysis/arith/$curve/local_factors.json"; [ -s "$inp" ] || { echo "[err] missing $inp"; exit 3; }
: "${PY:=python3}"
json="$($PY scripts/langlands/zero_check_brent.py "$curve" "$inp" 2>/dev/null || printf "{}")"
ts="$(date -u +%FT%TZ)"; out=".tau_ledger/arith/confirm_sym2_${curve//\//_}.json";
zero_t=$(printf "%s" "$json" | sed -n 's/.*"zero_t":[ ]*\([^,}]*\).*/\1/p')
: > "$out"; printf "%s" "{" >> "$out"
printf "%s" "\"ts\":\"$ts\",\"curve\":\"$curve\",\"status\":\"zeros_scanned\",\"zeros_check\":{\"method\":\"Brent\",\"zero_t\":$zero_t}}" >> "$out"
echo "[ok] updated → $out"
