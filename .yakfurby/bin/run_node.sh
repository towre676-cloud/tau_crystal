#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
. ".yakfurby/bin/helpers.sh"; load_cfg
log "yak-furby running id=$NODE_ID seconds=$CHUNK_SECONDS"
i=0
while :; do
  i=$((i+1))
  SEG_ID="$(date -u +%Y%m%dT%H%M%SZ)_${NODE_ID}_$i"
  .yakfurby/bin/capture_segment.sh "$SEG_ID" || log "capture failed seg=$SEG_ID"
  .yakfurby/bin/sense_env.sh "$SEG_ID" || true
  .yakfurby/bin/seal_segment.sh "$SEG_ID" || log "seal failed seg=$SEG_ID"
done
