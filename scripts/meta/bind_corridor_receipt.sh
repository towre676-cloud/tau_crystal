#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LBASE=".tau_ledger/lean_module_capsules"; LSEAL="$LBASE/capsule_set.seal.json"
RDIR=$(ls -1d run_20* 2>/dev/null | tail -n1 || echo "")
RREP=""; [ -n "$RDIR" ] && [ -f "$RDIR/report.json" ] && RREP="$RDIR/report.json"
[ -s "$LSEAL" ] || { echo "[err] missing lean seal $LSEAL"; exit 2; }
OUT="docs/ledger/corridor_receipt.json"; : > "$OUT"
printf "{" >> "$OUT"
printf "\"kind\":\"CorridorReceipt.v2\"," >> "$OUT"
printf "\"lean_capsule_set\":%s," "$(cat "$LSEAL")" >> "$OUT"
if [ -n "$RREP" ]; then printf "\"tau_reflection\":%s" "$(cat "$RREP")" >> "$OUT"; else printf "\"tau_reflection\":null" >> "$OUT"; fi
printf "}\n" >> "$OUT"
