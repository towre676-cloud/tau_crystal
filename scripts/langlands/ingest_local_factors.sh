cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
curve="${1:-}"; src="${2:-}";
[ -n "$curve" ] && [ -n "$src" ] && [ -s "$src" ] || { echo "[err] usage: ingest_local_factors.sh <curve> <path/to/local_factors.json>"; exit 2; }
dst="analysis/arith/$curve/local_factors.json"; mkdir -p "$(dirname "$dst")" ".tau_ledger/arith"
cp -f "$src" "$dst"
sha=$(openssl dgst -sha256 "$dst" | awk "{print \$2}")
nfac=$(grep -c "\"p\":" "$dst" || printf "0")
ts="$(date -u +%FT%TZ)"; out=".tau_ledger/arith/confirm_sym2_${curve//\//_}.json"
: > "$out"
printf "%s" "{" >> "$out"
printf "%s" "\"ts\":\"$ts\",\"curve\":\"$curve\",\"status\":\"inputs_ingested\",\"local_factors_present\":true," >> "$out"
printf "%s" "\"local_factors_path\":\"$dst\",\"local_factors_sha256\":\"$sha\",\"local_factor_count\":$nfac," >> "$out"
printf "%s" "\"gamma_factors\":\"Sym^2(E): Gamma_R(s+1)*Gamma_R(s)\"," >> "$out"
printf "%s" "\"satake_params\":\"pending\",\"completed_L\":\"pending\",\"zeros_check\":{\"method\":\"Brent\",\"found\":null},\"notes\":\"inputs ingested; zeros pending\"}" >> "$out"
echo "[ok] updated → $out"
