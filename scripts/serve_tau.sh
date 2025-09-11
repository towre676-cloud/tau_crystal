#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022
PORT=${PORT:-8787}
command -v openssl >/dev/null 2>&1 || { echo "[err] openssl not found on PATH"; exit 1; }
echo "[serve] listening on 127.0.0.1:${PORT} (openssl s_server)" >&2
while true; do
  coproc SSL { openssl s_server -quiet -accept "$PORT" -nocert -naccept 1; }
  bash scripts/handle_http.sh <&"${SSL[0]}" >&"${SSL[1]}" || true
  wait "$SSL_PID" 2>/dev/null || true
done
