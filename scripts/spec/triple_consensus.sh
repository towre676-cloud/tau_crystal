#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
report="analysis/triple_consensus.diff"; : > "$report"; ok=1
bash scripts/ops/verify_offline.sh >/dev/null 2>&1 || { echo "[bash] FAIL" | tee -a "$report"; ok=0; }
if command -v lake >/dev/null 2>&1; then lake exe verify-chain >/dev/null 2>&1 || { echo "[lean] FAIL" | tee -a "$report"; ok=0; }
else echo "[lean] SKIP" | tee -a "$report"; fi
if [ -x ./tau_verify ]; then ./tau_verify . >/dev/null 2>&1 || { echo "[rust] FAIL" | tee -a "$report"; ok=0; }
else echo "[rust] SKIP" | tee -a "$report"; fi
if [ "${TAU_REQUIRE_TRIPLE:-1}" -eq 1 ]; then
  need=1; command -v lake >/dev/null 2>&1 && need=$((need+1)); [ -x ./tau_verify ] && need=$((need+1))
  b=$([ -s "$report" ] && grep -c '\[bash] FAIL' "$report" || echo 0); b=$((b==0))
  l=$([ -s "$report" ] && grep -c '\[lean] FAIL' "$report" || echo 0); l=$((l==0 && $(command -v lake >/dev/null 2>&1; echo $?)==0))
  r=$([ -s "$report" ] && grep -c '\[rust] FAIL' "$report" || echo 0); r=$((r==0 && -x ./tau_verify))
  got=$((b + l + r))
  [ "$got" -lt "$need" ] && { echo "[consensus] FAIL ($got/$need) — see $report"; exit 7; }
fi
exit $(( ok==1 ? 0 : 6 ))
