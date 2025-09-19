#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
label="${1:-11a1}"
aptsv="${2:-analysis/atlas/${label}/ap.tsv}"
atlas="analysis/atlas.jsonl"; touch "$atlas"
[ -s "$aptsv" ] || { echo "[adv] no ap.tsv: $aptsv"; exit 4; }
seed=$(scripts/meta/_sha256.sh "$atlas" 2>/dev/null || echo 0)
n=$(awk "END{print NR}" "$aptsv")
[ "$n" -gt 1 ] || { echo "[adv] ap.tsv too short"; exit 5; }
hex=$(printf "%s" "$seed" | tr -cd "0-9A-Fa-f" | head -c 12)
[ -n "$hex" ] || hex=0
body=$(( n-1 ))
ix0=$(( (0x$hex % body) + 1 ))
ln=$(( ix0 + 1 ))
line=$(awk -v ln="$ln" "NR==ln{print;exit}" "$aptsv")
p=$(printf "%s\n" "$line" | awk "{print \$1}")
ap_ref=$(printf "%s\n" "$line" | awk "{print \$2}")
[ "$p" -gt 2 ] 2>/dev/null || { echo "[adv] invalid p: $p"; exit 6; }
coeffs=$(python3 scripts/assure/_coeffs_from_atlas.py "$label" 2>/dev/null || echo "NA NA NA NA NA")
a1=$(printf "%s\n" "$coeffs" | awk "{print \$1}")
a2=$(printf "%s\n" "$coeffs" | awk "{print \$2}")
a3=$(printf "%s\n" "$coeffs" | awk "{print \$3}")
a4=$(printf "%s\n" "$coeffs" | awk "{print \$4}")
a6=$(printf "%s\n" "$coeffs" | awk "{print \$5}")
[ "$a1" != "NA" ] && [ "$a2" != "NA" ] && [ "$a3" != "NA" ] && [ "$a4" != "NA" ] && [ "$a6" != "NA" ] || { echo "[adv] coeff parse failed for $label"; exit 8; }
ap_awk=$(awk -f scripts/assure/_ap_recount.awk -v p="$p" -v a1="$a1" -v a2="$a2" -v a3="$a3" -v a4="$a4" -v a6="$a6")
ap_py=$(python3 scripts/assure/_ap_recount.py "$p" "$a1" "$a2" "$a3" "$a4" "$a6" 2>/dev/null || echo "NaN")
agree_dual=$([ "$ap_awk" = "$ap_py" ] && echo true || echo false)
agree_ref=$([ "$ap_awk" = "$ap_ref" ] && [ "$ap_py" = "$ap_ref" ] && echo true || echo false)
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null || python -c "import datetime;print(datetime.datetime.utcnow().strftime(\"%Y-%m-%dT%H:%M:%SZ\"))")
g=$(git rev-parse --short=12 HEAD 2>/dev/null || echo "nogit")
out=".tau_ledger/adversarial/lottery_${label}_p${p}_${ts//[:]/-}.json"; : > "$out"
printf "%s\n" "{" >> "$out"
printf "%s\n" "  \"schema\":\"taucrystal/adversarial_recount/v1\"," >> "$out"
printf "%s\n" "  \"label\":\"$label\",\"p\":$p,\"index\":$ix0," >> "$out"
printf "%s\n" "  \"ap_ref\":$ap_ref,\"ap_awk\":$ap_awk,\"ap_py\":$ap_py," >> "$out"
printf "%s\n" "  \"agree_dual\":$agree_dual,\"agree_ref\":$agree_ref," >> "$out"
printf "%s\n" "  \"commit\":\"$g\",\"ts\":\"$ts\"" >> "$out"
printf "%s\n" "}" >> "$out"
printf "%s\n" "{\"type\":\"ADVERSARIAL_RECOUNT\",\"label\":\"$label\",\"p\":$p,\"agree\":$agree_ref,\"ts\":\"$ts\"}" >> "$atlas"
echo "[adv] label=$label p=$p ref=$ap_ref awk=$ap_awk py=$ap_py agree_ref=$agree_ref agree_dual=$agree_dual (ix0=$ix0)"
