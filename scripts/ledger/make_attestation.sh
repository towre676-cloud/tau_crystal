#!/usr/bin/env bash
set -euo pipefail
LEDGER_DIR=".tau_ledger"
CHAIN="${LEDGER_DIR}/CHAIN"
OUT="${LEDGER_DIR}/attestation.txt"
N="${ATTEST_TAIL_N:-10}"

[ -f "$CHAIN" ] || { echo "[attest] no chain yet at $CHAIN" >&2; exit 0; }

head_hash="$(tail -n1 "$CHAIN" | awk '{print $1}')"
count="$(wc -l < "$CHAIN" | tr -d ' ')"
ts="$(date -u +'%Y-%m-%dT%H:%M:%SZ')"

{
  echo "== τ‑Crystal Attestation =="
  echo "generated: ${ts}"
  echo "chain_head: ${head_hash}"
  echo "receipts_total: ${count}"
  echo
  echo "-- last ${N} receipts --"
} > "$OUT"

tail -n "$N" "$CHAIN" | awk '{print $2}' | while read -r rcpt; do
  # extract fields without jq
  # safe defaults if keys missing
  id=$(  grep -oE '"id"[[:space:]]*:[[:space:]]*"[^"]*"'           "$rcpt" | sed -E 's/.*"id"[[:space:]]*:[[:space:]]*"([^"]*)".*/\1/' )
  ts=$(  grep -oE '"ts"[[:space:]]*:[[:space:]]*"[^"]*"'           "$rcpt" | sed -E 's/.*"ts"[[:space:]]*:[[:space:]]*"([^"]*)".*/\1/' )
  git=$( grep -oE '"git"[[:space:]]*:[[:space:]]*"[^"]*"'          "$rcpt" | sed -E 's/.*"git"[[:space:]]*:[[:space:]]*"([^"]*)".*/\1/' )
  plan=$(grep -oE '"plan"[[:space:]]*:[[:space:]]*"[^"]*"'         "$rcpt" | sed -E 's/.*"plan"[[:space:]]*:[[:space:]]*"([^"]*)".*/\1/' )
  merkle=$(grep -oE '"merkle_root"[[:space:]]*:[[:space:]]*"[^"]*"' "$rcpt" | sed -E 's/.*"merkle_root"[[:space:]]*:[[:space:]]*"([^"]*)".*/\1/' )
  # receipt file hash is stored in CHAIN; recompute to show local integrity too
  rhash=$(sha256sum "$rcpt" | awk '{print $1}')
  echo "id=${id} ts=${ts} plan=${plan} git=${git} hash=${rhash} merkle=${merkle}"
done >> "$OUT"

echo "[attest] wrote ${OUT}" >&2
