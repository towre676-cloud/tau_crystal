#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -e
HEEGNER_ZONE=".tau_ledger/heegner/zone_reference.json"
CURRENT=".tau_ledger/runtime/current_entropy.json"
LIMIT_FILE=".tau_ledger/stability/thresholds.json"
LIMIT=$(jq -r '.heegner_entropy_bound' "$LIMIT_FILE" 2>/dev/null || echo 0.008)

[ -s "$HEEGNER_ZONE" ] && [ -s "$CURRENT" ] || { echo "[ERR] missing entropy inputs"; exit 2; }

DELTA=$(jq -s '.[0].entropy_vector as $a | .[1].entropy_vector as $b
  | if ($a|length)!=( $b|length ) then halt_error(4)
    else [$a,$b]|transpose|map((.[0]-.[1])*(.[0]-.[1]))|add|sqrt end' \
  "$HEEGNER_ZONE" "$CURRENT" 2>/dev/null || true)

[ -n "${DELTA:-}" ] || { echo "[ERR] entropy vectors invalid/mismatched"; exit 4; }

awk -v delta="$DELTA" -v limit="$LIMIT" 'BEGIN{
  if (delta+0.0 > limit+0.0){ printf "[ALERT] Entropy drift exceeds Heegner bound: %.6f\n", delta; exit 88 }
  else { printf "[OK] Entropy within Heegner bound: %.6f\n", delta; exit 0 }
}'
