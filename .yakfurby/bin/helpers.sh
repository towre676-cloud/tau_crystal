#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
log(){ printf "[%s] %s\n" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$*" | tee -a ".yakfurby/log/node.log" ; }
die(){ log "FATAL: $*"; exit 1; }
have(){ command -v "$1" >/dev/null 2>&1; }
sha256_file(){ sha256sum "$1" | awk "{print \$1}"; }
load_cfg(){ . ".yakfurby/cfg/node.conf"; mkdir -p "$CAPS_DIR" "$LEDGER_DIR" "$RUNTIME_DIR" "$LOG_DIR"; }
