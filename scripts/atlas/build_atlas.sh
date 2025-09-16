#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1

mkdir -p atlas

CHAIN=".tau_ledger/chain/CHAIN"
FUSED="analysis/fused_gates.json"
LAUR="analysis/laurent_ring.tsv"
HEEG="analysis/analytic_heegner.tsv"
HITS="analysis/discovery_hits.tsv"
BEST="analysis/discovery_best.tsv"
ROLL="analysis/rollup_summary.tsv"

IDX="atlas/index.tsv"
R2="atlas/rank2.tsv"
SZ="atlas/simple_zero.tsv"
LU="atlas/laurent_unit.tsv"
DTOP="atlas/discovery_top.tsv"
README="atlas/README.md"

# --- helpers (bash/awk only) -------------------------------------------------
ts=""; [ -s "$CHAIN" ] && ts="$(tail -n1 "$CHAIN" | awk '{print $1}' | tr -d '\r\n')"
fused_pass=""; [ -s "$FUSED" ] && fused_pass="$(grep -o '"fused_pass":[^,}]*' -m1 "$FUSED" | sed 's/.*://; s/[[:space:]]//g')"
laur_blk="";  [ -s "$FUSED" ] && laur_blk="$(grep -o '"laurent":[^}]*}' -m1 "$FUSED" || true)"
laur_pass="false"; echo "$laur_blk" | grep -q 'pass":[[:space:]]*true' && laur_pass="true"

phi=""; L0=""; slope_avg=""; curve_avg=""; sc=""; domp=""; domr=""; fe=""; rankg=""
if [ -s "$HEEG" ]; then
  # heeg TSV cols: 1 phi | 2 L0 | 3 Lp | 4 Omega | 5 Height | 6 deltas | 7 scales | 8 sign_changes | 9 slope_avg | 10 curve_avg | 11 dom_p | 12 dom_ratio | 13 fe_consistency | 14 rank_guess
  read -r phi L0 _ _ _ _ _ sc slope_avg curve_avg domp domr fe rankg < <(tail -n1 "$HEEG" | awk -F'\t' '{printf "%s %s x x x x x %s %s %s %s %s %s\n",$1,$2,$8,$9,$10,$11,$12,$13,$14}')
fi

mean_r=""; best_N=""; best_k=""; tested=""
if [ -s "$BEST" ]; then
  read -r mean_r best_N best_k tested _ _ < <(awk 'NR==1{print; exit}' "$BEST")
fi

seed=""; [ -s analysis/passport_sig.tsv ] && seed="$(awk -v key=nonce_hex -v def="" -f scripts/tools/read_kv2.awk analysis/passport_sig.tsv 2>/dev/null || true)"
[ -z "$seed" ] && [ -s "$FUSED" ] && seed="$(grep -o '"nonce":"[0-9a-fA-F]\{16,64\}"' -m1 "$FUSED" | sed 's/.*"nonce":"//; s/".*//' || true)"
seed_pref="$(echo "$seed" | tr -dc '0-9a-fA-F' | cut -c1-16)"

# --- index header -------------------------------------------------------------
if [ ! -s "$IDX" ]; then
  printf "ts\tfused_pass\tlaurent_pass\trank_guess\tsign_changes\tL0\tslope_avg\tcurve_avg\tdom_p\tdom_ratio\tfe_consistency\tmean_r\tN\tk\ttested\tseed_prefix\n" > "$IDX"
fi

# --- append snapshot row ------------------------------------------------------
printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" \
  "${ts:-NA}" "${fused_pass:-NA}" "${laur_pass:-false}" "${rankg:-NA}" "${sc:-NA}" \
  "${L0:-NA}" "${slope_avg:-NA}" "${curve_avg:-NA}" "${domp:-NA}" "${domr:-NA}" "${fe:-NA}" \
  "${mean_r:-NA}" "${best_N:-NA}" "${best_k:-NA}" "${tested:-NA}" \
  "${seed_pref:-}" >> "$IDX"

# --- derived views ------------------------------------------------------------
# rank≥2 view
awk -F'\t' 'NR==1||($4+0>=2){print}' "$IDX" > "$R2"

# simple-zero (sign changes) view
awk -F'\t' 'NR==1||($5+0>=1){print}' "$IDX" > "$SZ"

# laurent unit-circle pass view
awk -F'\t' 'NR==1||$3=="true"{print}' "$IDX" > "$LU"

# top discoveries by mean_r (smallest first; keep header+top 50)
{ head -n1 "$IDX"; tail -n +2 "$IDX" | awk -F'\t' '$12!~/^NA$/ {print}' | sort -t$'\t' -k12,12g | head -n 50; } > "$DTOP"

# --- README.md summary --------------------------------------------------------
r2c=$(awk 'NR>1{if($4+0>=2)c++} END{print c+0}' "$IDX")
szc=$(awk 'NR>1{if($5+0>=1)c++} END{print c+0}' "$IDX")
luc=$(awk 'NR>1{if($3=="true")c++} END{print c+0}' "$IDX")
tot=$(awk 'END{print NR-1}' "$IDX")

medL0="NA"; [ -s "$HEEG" ] && medL0="$(awk -F'\t' 'NR>1{L0[++n]=$2+0} END{ if(n){asort(L0); m=int((n+1)/2); print (n%2?L0[m]:(L0[m]+L0[m+1])/2)} else print "NA"}' "$HEEG")"
ad10="NA"; ad05="NA"
[ -s "$ROLL" ] && ad10="$(awk -F'\t' '$1=="adaptive_tau_L0_10pct"{print $2}' "$ROLL" 2>/dev/null || echo NA)"
[ -s "$ROLL" ] && ad05="$(awk -F'\t' '$1=="adaptive_tau_L0_5pct"{print $2}' "$ROLL" 2>/dev/null || echo NA)"

{
  echo "# Atlas"
  echo
  echo "- Total snapshots: **$tot**"
  echo "- Rank ≥ 2 candidates: **$r2c**"
  echo "- Simple-zero (sign change) snapshots: **$szc**"
  echo "- Laurent unit pass: **$luc**"
  echo "- Median L0: **$medL0**  |  Adaptive τ(L0): 10% **$ad10**, 5% **$ad05**"
  echo
  echo "## Files"
  echo "- \`atlas/index.tsv\` — all snapshots"
  echo "- \`atlas/rank2.tsv\` — rank≥2 candidates"
  echo "- \`atlas/simple_zero.tsv\` — sign-change snapshots"
  echo "- \`atlas/laurent_unit.tsv\` — Laurent unit-circle passes"
  echo "- \`atlas/discovery_top.tsv\` — best discovery means (≤50)"
} > "$README"

echo "[atlas] updated:"
echo " - $IDX"
echo " - $R2"
echo " - $SZ"
echo " - $LU"
echo " - $DTOP"
echo " - $README"
