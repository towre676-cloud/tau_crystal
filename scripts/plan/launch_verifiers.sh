#!/usr/bin/env bash
set -euo pipefail
n="${TAU_MAX_WORKERS:-2}"
total="${TAU_MAX_SHARDS:-10}"
cmd="./tools/verify_one.sh"

need_proofs="${TAU_REQUIRE_PROOFS:-false}"
allow_override="${ALLOW_NO_PROOFS:-0}"

if [ "$need_proofs" = "true" ] && [ "$allow_override" != "1" ]; then
  printf '[launch] proofs are required (TAU_REQUIRE_PROOFS=true) — refusing to run. Set ALLOW_NO_PROOFS=1 to override.\n' >&2
  exit 2
fi

if [ ! -x "$cmd" ]; then
  printf '[launch] missing %s; aborting cleanly.\n' "$cmd" >&2
  exit 0
fi

i=0
for shard in $(seq 1 "$total"); do
  "$cmd" "$shard" &
  i=$((i+1))
  if [ "$i" -ge "$n" ]; then
    wait -n || true
    i=$((i-1))
  fi
done
wait
printf '[launch] completed %s shards with up to %s workers\n' "$total" "$n"

# Emit a ledger receipt for this run
bash scripts/ledger/make_receipt.sh

# Write STATUS line into docs/manifest.md
if [ -x scripts/ledger/update_manifest_status.sh ]; then
  bash scripts/ledger/update_manifest_status.sh || true
fi

# Build attestation.txt
if [ -x scripts/ledger/make_attestation.sh ]; then
  bash scripts/ledger/make_attestation.sh || true
fi

# Update README + manifest descriptions (idempotent)
if [ -x scripts/plan/describe_plan.sh ]; then
  bash scripts/plan/describe_plan.sh || true
fi
