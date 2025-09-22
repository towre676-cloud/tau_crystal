#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
stamp="${1:-$(date -u +%Y%m%dT%H%M%SZ)}"
ntp_time=$(curl -s http://worldtimeapi.org/api/timezone/UTC | jq -r .datetime | cut -d. -f1)
ntp_ts=$(date -u -d "$ntp_time" +%s)
stamp_ts=$(date -u -d "${stamp//Z/}" +%s)
drift=$((ntp_ts - stamp_ts))
[ "${drift#-}" -le 300 ] || { echo "[err] $0: operation failed; check input and try again
echo "[OK] timestamp valid: $stamp"
