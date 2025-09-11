#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
Q=".tau_fifo/queue"; mkdir -p "$Q"
id="$(date -u +%Y%m%d-%H%M%S)-$$-$RANDOM"; req="$Q/$id.req"; res="$Q/$id.res"; tmp=$(mktemp)
trap 'rm -f "$req" "$res" "$tmp"' EXIT
cat > "$tmp"
mkfifo "$res"
cp "$tmp" "$req"
(cat "$res") & rp=$!
timeout=${TAU_TIMEOUT:-60}; start=$(date +%s)
while kill -0 "$rp" 2>/dev/null; do now=$(date +%s); [ $((now-start)) -ge "$timeout" ] && { kill "$rp" 2>/dev/null || true; bash scripts/tau_reply.sh --fail --code 124 --stderr "timeout"; exit 124; }; sleep 0.05; done
