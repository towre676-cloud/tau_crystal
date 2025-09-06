#!/usr/bin/env bash
set -u
DOMAIN="${1:-P2P}"
TOPIC="${2:-erp.events.P2P}"
if command -v kcat >/dev/null 2>&1 && [ -n "${KCAT_BROKERS:-}" ]; then
  exec kcat -b "$KCAT_BROKERS" -t "$TOPIC" -C -f '%s\n' -q
elif command -v nats >/dev/null 2>&1 && [ -n "${NATS_URL:-}" ]; then
  exec nats sub "$TOPIC" --server "$NATS_URL" --raw --headers=false
else
  echo "[subscribe] using tmp/${DOMAIN}.ndjson (tail -F)" 1>&2
  mkdir -p tmp
  touch "tmp/${DOMAIN}.ndjson"
  exec tail -n+1 -F "tmp/${DOMAIN}.ndjson"
fi
