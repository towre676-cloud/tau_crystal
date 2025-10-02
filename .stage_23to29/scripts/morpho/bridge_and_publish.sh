#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
now=$(date -u +%Y%m%dT%H%M%SZ)
gitrev=$(git rev-parse --short=10 HEAD 2>/dev/null || echo nogit)
run="run_${now}_${gitrev}"
pack="analysis/morpho/packs/$run"; mkdir -p "$pack"
if [ -x scripts/geom/strict_ci.sh ]; then
  scripts/geom/strict_ci.sh || { echo "geom strict gate failed"; exit 7; }
fi
cert=$(ls -1t analysis/morpho/certificates/cert_*.json 2>/dev/null | head -n 1 || true)
[ -n "$cert" ] || { echo "no morpho certificate found"; exit 2; }
glob=".tau_ledger/morpho/global.L"; [ -f "$glob" ] || { echo "missing global.L"; exit 3; }
locals=( .tau_ledger/morpho/*.local )
[ -f "${locals[0]}" ] || { echo "no morpho locals"; exit 4; }
geom_tx="analysis/geom/transcript.tsv"; [ -f "$geom_tx" ] || geom_tx=""
geom_dot="analysis/geom/proof.dot";     [ -f "$geom_dot" ] || geom_dot=""
cp -f "$cert" "$pack/"; cp -f "$glob" "$pack/"
for f in "${locals[@]}"; do cp -f "$f" "$pack/"; done
[ -n "$geom_tx" ] && cp -f "$geom_tx" "$pack/" || true
[ -n "$geom_dot" ] && cp -f "$geom_dot" "$pack/" || true
for x in /mnt/data/morpho_receipt_manifest.json /mnt/data/morpho_receipt_metrics.tsv /mnt/data/morpho_receipt_proof_note.txt /mnt/data/frontal_report.json /mnt/data/frontal_report.md; do
  [ -f "$x" ] && cp -f "$x" "$pack/";
done
rec="$pack/corridor.receipt.tsv"; : > "$rec"
printf "%s\n" "RUN=$run"                >> "$rec"
printf "%s\n" "TIME=$now"               >> "$rec"
printf "%s\n" "GIT=$gitrev"             >> "$rec"
printf "%s\t%s\n" "FILE" "$(basename "$cert")" >> "$rec"
for f in "$pack"/*; do
  bn=$(basename "$f"); h=$(sha256sum "$f" | awk "{print \$1}"); printf "%s\t%s\t%s\n" "SHA256" "$bn" "$h" >> "$rec"
done
Hbar=$(awk -F[\":,] '{for(i=1;i<=NF;i++) if($i~/h_bar/){gsub(/^[[:space:]]+|[[:space:]]+$/,"",$(i+1)); print $(i+1); exit}}' "$pack/$(basename "$cert")")
printf "%s\n" "H_BAR=$Hbar"            >> "$rec"
root=$(awk '$1=="SHA256"{print $3}' "$rec" | LC_ALL=C sort | tr -d "\n" | sha256sum | awk "{print \$1}")
printf "%s\n" "MERKLE_SIM=$root"       >> "$rec"
echo "published: $pack  (H_BAR=$Hbar, files=$(ls -1 "$pack" | wc -l), root=$root)"
