#!/usr/bin/env bash
set -euo pipefail
J=$(printf "%s\n" .tau_ledger/freed/z4c_resstudy_*.json 2>/dev/null | LC_ALL=C sort | tail -n1)
[ -f "$J" ] || { echo "[err] no z4c_resstudy_*.json"; exit 1; }
echo ">> validating $J"
jq -e '.stable == true' "$J" >/dev/null || { echo "[fail] stable=false"; exit 2; }
# choose integrated orders if present, else plain orders
jq -e '((.I_orders // .orders) | (.H // 0) > 0 and (.M // 0) > 0 and (."C_Gamma" // 0) > 0)' "$J" >/dev/null \
  || { echo "[fail] nonpositive convergence order"; exit 3; }
# advantage: step - glued < 0 for each channel at every resolution (prefer integrated deltas if present)
jq -e 'all(.deltas[]; ((.IH // .H) // 1e99) < 0 and ((.IM // .M) // 1e99) < 0 and ((.ICG // ."C_Gamma") // 1e99) < 0)' "$J" >/dev/null \
  || { echo "[fail] corridor advantage not consistent (Δ>=0 somewhere)"; exit 4; }
echo "[ok] guard passed"
