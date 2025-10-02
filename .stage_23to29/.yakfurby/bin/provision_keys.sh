#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
. ".yakfurby/bin/helpers.sh"; load_cfg
PUB="$KEYS_DIR/ed25519.pub"; SEC="$KEYS_DIR/ed25519.sec"; mkdir -p "$KEYS_DIR"
[ -f "$SEC" ] && [ -f "$PUB" ] && { log "keys present"; exit 0; }
if have ssh-keygen; then ssh-keygen -t ed25519 -N "" -C "$NODE_ID" -f "$KEYS_DIR/ed25519" >/dev/null 2>&1 || true; fi
if [ -f "$KEYS_DIR/ed25519" ] && [ -f "$KEYS_DIR/ed25519.pub" ]; then mv "$KEYS_DIR/ed25519" "$SEC"; mv "$KEYS_DIR/ed25519.pub" "$PUB"; chmod 600 "$SEC"; log "software ed25519 keys provisioned"; exit 0; fi
die "no ssh-keygen; please install or pre-provide $SEC and $PUB"
