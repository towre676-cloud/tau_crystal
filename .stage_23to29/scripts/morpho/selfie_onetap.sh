#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022

# Usage: selfie_onetap.sh <selfieA.tsv> <selfieB.tsv> [subject_id] [threshold]
A="${1:-}"; B="${2:-}"; SUBJ="${3:-selfie}"; TH="${4:-0.0100}"
[ -n "$A" ] && [ -s "$A" ] && [ -n "$B" ] && [ -s "$B" ] || { echo "Put two landmark files on disk first: A and B (x<TAB>y per line)."; exit 2; }
scripts/morpho/lean_geom_chain.sh "$A" "$SUBJ" >/dev/null || { echo "Lean stub failed"; exit 3; }
scripts/morpho/zk_diff_chain.sh "$A" "$B" "$TH" || { echo "Could not compare A vs B"; exit 4; }
REC="$(ls -1t .tau_ledger/morpho/zk/*.receipt.json 2>/dev/null | head -n 1)"
[ -n "$REC" ] && [ -s "$REC" ] || { echo "No comparison receipt written"; exit 5; }
VAL="$(command -v jq >/dev/null 2>&1 && jq -r ".value" "$REC" || awk -F\" "/\\"value\\":/{print \$4; exit}" "$REC")"
ACC="$(command -v jq >/dev/null 2>&1 && jq -r ".accept" "$REC" || awk -F[,:\\ }]+ "/accept/{print \$2; exit}" "$REC")"
scripts/morpho/tau_sheaf_couple.sh "$REC" subject="$SUBJ" metric=RMS value="$VAL" tag=morpho note="A vs B bathroom-selfie check" >/dev/null || true
echo
echo "✅ Bathroom‑Selfie Check Complete"
echo "Subject: $SUBJ   Threshold: $TH   RMS: $VAL   Accept(≤TH): $ACC"
echo
echo "Receipts & outputs you now own:"
echo "  • Comparison receipt: $REC"
echo "  • Lean stub: TauCrystal/GeomProofs/$(basename "${A%.*}").lean"
echo "  • τ‑sheaf log (append‑only): .tau_ledger/tau_sheaf/events.jsonl"
echo "  • Analytics table: analysis/morpho/tau_coupling.tsv"
echo
if [ "$ACC" = "1" ] || [ "$ACC" = "true" ]; then
  echo "Result: These two selfies match within the chosen tolerance. This is provably derived from your pixels."
else
  echo "Result: Outside tolerance. Either different pose/lighting moved landmarks too far, or it is not the same face at this precision."
fi
