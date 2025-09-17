#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
log=".tau_ledger/metrics.jsonl"
ts="$(date -u +%Y%m%dT%H%M%SZ)"
head_line=$(tail -n1 .tau_ledger/CHAIN 2>/dev/null || true)
hh="$(awk '{print $1}' <<<"$head_line")"
rp="$(awk '{print $2}' <<<"$head_line")"
re=$(jq -r '.laurent.re // null' analysis/fused_gates.json 2>/dev/null || echo null)
im=$(jq -r '.laurent.im // null' analysis/fused_gates.json 2>/dev/null || echo null)
printf '{"ts":"%s","head_hash":"%s","receipt":"%s","laurent":{"re":%s,"im":%s}}\n' "$ts" "$hh" "$rp" "$re" "$im" >> "$log"
echo "[metrics] appended to $log"
