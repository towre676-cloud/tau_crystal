#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
mkdir -p analysis/metrics
out="analysis/metrics/consensus.jsonl"

ok_bash=0; ok_lean=0; ok_rust=0

# Bash offline verify
if bash scripts/ops/verify_offline.sh >/dev/null 2>&1; then ok_bash=1; fi

# Lean chain link (if lake/lean present)
if command -v lake >/dev/null 2>&1; then
  if lake exe verify-chain >/dev/null 2>&1; then ok_lean=1; fi
fi

# Rust sealed binary (if present)
if [ -x ./tau_verify ]; then
  if ./tau_verify . >/dev/null 2>&1; then ok_rust=1; fi
fi

sum=$((ok_bash+ok_lean+ok_rust))
verdict="fail"; [ "$sum" -eq 3 ] && verdict="pass"
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
head_hash=$(tail -n1 .tau_ledger/CHAIN | awk '{print $1}')
jq -n --arg ts "$ts" --arg v "$verdict" --arg hh "$head_hash" \
      --argjson bash "$ok_bash" --argjson lean "$ok_lean" --argjson rust "$ok_rust" \
      '{timestamp:$ts, verdict:$v, head:$hh, bash:$bash, lean:$lean, rust:$rust}' >> "$out"

echo "[consensus] 3-of-3: $verdict (bash=$ok_bash lean=$ok_lean rust=$ok_rust) → $out"
[ "${TAU_REQUIRE_TRIPLE:-1}" = "1" ] && [ "$verdict" != "pass" ] && exit 7 || true
