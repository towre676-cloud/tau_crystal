#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
# Usage: replay_witness.sh <pack.tgz>  (or --latest to pick most recent in .tau_ledger/discovery/)
pack="${1:-}"
[ -z "$pack" ] && { echo "[replay] usage: replay_witness.sh <witness.tar.gz|--latest>"; exit 2; }

if [ "$pack" = "--latest" ]; then
  pack=$(ls -1t .tau_ledger/discovery/witness-*.tar.gz 2>/dev/null | head -n1 || true)
  [ -n "$pack" ] || { echo "[replay] no witness packs found"; exit 0; }
fi

tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
tar -xzf "$pack" -C "$tmp"
echo "[replay] unpacked → $tmp"

if [ ! -x ./tau_verify ]; then echo "[replay] missing ./tau_verify"; exit 3; fi
./tau_verify "$tmp" >/dev/null

# Compare hash of receipt inside pack vs recomputed (mint local receipt)
orig=$(jq -r '.hash // empty' "$tmp/receipt.json")
[ -z "$orig" ] && orig=$(sha256sum "$tmp/receipt.json" 2>/dev/null | awk '{print $1}')
bash scripts/ops/assure_strict.sh >/dev/null
head_hash=$(tail -n1 .tau_ledger/CHAIN | awk '{print $1}')

ok=$([ "$orig" = "$head_hash" ] && echo 1 || echo 0)
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
jq -n --arg ts "$ts" --arg pack "$pack" --arg orig "$orig" --arg now "$head_hash" \
      --arg verdict "$([ "$ok" -eq 1 ] && echo pass || echo fail)" \
      '{timestamp:$ts, pack:$pack, receipt_in_pack:$orig, local_head:$now, verdict:$verdict}' \
      >> analysis/metrics/replay.jsonl

[ "$ok" -eq 1 ] && echo "[replay] OK: pack receipt = local head" || { echo "[replay] MISMATCH"; exit 9; }
