#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
PORT=${PORT:-8787}
command -v socat >/dev/null 2>&1 || { echo "[bridge] socat not found"; exit 1; }
echo "[bridge] http on 127.0.0.1:${PORT} (socat)" >&2
while :; do
  socat -T 60 -d -d TCP-LISTEN:"$PORT",reuseaddr,fork SYSTEM:"bash scripts/http_handler.sh" 2>> .tau_fifo/logs/http.socat.log || true
done
