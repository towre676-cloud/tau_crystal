#!/usr/bin/env bash
set +H
. scripts/plumbing/_lib.sh || exit 1
BOX_ID="${1:?box id}"; SHIFT="${2:?integer shift}"
case "$SHIFT" in -|*[!0-9-]*) echo "SHIFT must be integer"; exit 1;; esac
safe_mkdir ".tau_ledger/hysteresis/$BOX_ID"
parity=$(python -c "import sys; s=int(sys.argv[1]); print((-1)**s)" "$SHIFT" 2>/dev/null || echo 1)
out=".tau_ledger/hysteresis/$BOX_ID/framing_${SHIFT}.json"
write_json "$out" "box_id" "$BOX_ID" "framing_shift" "$SHIFT" "phase_parity" "$parity" "at" "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
log "framing_phase: $BOX_ID shift=$SHIFT parity=$parity -> $out"
