#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
. ".yakfurby/bin/helpers.sh"; load_cfg
: "${NODE_ID:?NODE_ID missing in .yakfurby/cfg/node.conf}"
SEG_ID="test_$(date -u +%Y%m%dT%H%M%SZ)_${NODE_ID}_0"
".yakfurby/bin/capture_segment.sh" "$SEG_ID"
".yakfurby/bin/seal_segment.sh" "$SEG_ID"
log "smoke complete: $CAPS_DIR/${SEG_ID}.cap.tar"
