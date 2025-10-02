#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
. ".yakfurby/bin/helpers.sh"; load_cfg
N="${1:-5}"
log "quick run: N=$N, id=$NODE_ID, chunk=${CHUNK_SECONDS}s"
for i in $(seq 1 "$N"); do
  SEG_ID="$(date -u +%Y%m%dT%H%M%SZ)_${NODE_ID}_$i"
  .yakfurby/bin/capture_segment.sh "$SEG_ID" || log "capture failed seg=$SEG_ID"
  .yakfurby/bin/sense_env.sh "$SEG_ID" || true
  .yakfurby/bin/seal_segment.sh "$SEG_ID" || log "seal failed seg=$SEG_ID"
done
.yakfurby/bin/verify_chain.sh || true
log "quick run complete; capsules in $CAPS_DIR"
