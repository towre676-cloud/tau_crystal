#!/usr/bin/env bash
set +H; umask 022
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
A=".tau_ledger/last_run_A.json"; B=".tau_ledger/last_run_B.json"
prev=""
while :; do
  sig=$(printf "%s%s" "$(stat -c %%Y "$A" 2>/dev/null || echo 0)" "$(stat -c %%Y "$B" 2>/dev/null || echo 0)")
  [ "$sig" != "$prev" ] && { prev="$sig"; bash scripts/coho/morphism_live.sh "$A" "$B" || true; }
  sleep 3
done
