#!/usr/bin/env bash
set +e; set +H; umask 022
. scripts/coho/lib_json.sh
JSON="$1"; OUT="$2"; [ -n "$OUT" ] || OUT=".tau_ledger/leafvec.tmp.tsv"
ID=$(jstr "$JSON" id); [ -n "$ID" ] || ID="unknown_$(date +%s)"
# Strategy: prefer embedded leaves array if present; else read fallback .lst
LEAFS=$(sed -n -E "s/^[[:space:]]*\"leaves\"[[:space:]]*:[[:space:]]*\\[\\s*(.*)\\s*\\].*/\\1/p" "$JSON" | head -n1)
: > "$OUT"
if [ -n "$LEAFS" ]; then
  echo "$LEAFS" | tr "," "\n" | sed -E "s/^[[:space:]]*\"([^\"]*)\"[[:space:]]*$/\\1/" | awk -v id="$ID" 'NF{printf "%s\t%s\t1\n", id,$0}' >> "$OUT"
else
  F=".tau_ledger/leaves_${ID}.lst"; if [ -f "$F" ]; then
    awk -v id="$ID" 'NF{printf "%s\t%s\t1\n", id,$0}' "$F" >> "$OUT"
  else
    echo "::warn::no leaves in $JSON and no $F"
  fi
fi
echo "$OUT"
