#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
log=".tau_ledger/metrics.jsonl"
ts="$(date -u +%Y%m%dT%H%M%SZ)"
head_line=$(tail -n1 .tau_ledger/CHAIN 2>/dev/null || true)
head_hash="$(awk '{print $1}' <<<"$head_line")"
receipt_path="$(awk '{print $2}' <<<"$head_line")"
laurent_re="$(jq -r '.laurent.re // empty' analysis/fused_gates.json 2>/dev/null || true)"
laurent_im="$(jq -r '.laurent.im // empty' analysis/fused_gates.json 2>/dev/null || true)"
printf '{"ts":"%s","head_hash":"%s","receipt":"%s","laurent":{"re":%s,"im":%s}}\n' \
  "$ts" "$head_hash" "$receipt_path" "${laurent_re:-null}" "${laurent_im:-null}" >> "$log"
echo "[metrics] appended to $log"
