#!/usr/bin/env bash
set +H
. scripts/plumbing/_lib.sh || exit 1
BOX_ID="${1:-box-default}"
DISC="${2:--23}"
LEVEL="${3:-1}"
safe_mkdir ".tau_ledger/hysteresis/$BOX_ID"
meta=".tau_ledger/hysteresis/$BOX_ID/box.json"
write_json "$meta" "box_id" "$BOX_ID" "disc_D" "$DISC" "level_N" "$LEVEL" "created_at" "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
log "box_build: $BOX_ID D=$DISC N=$LEVEL -> $meta"
