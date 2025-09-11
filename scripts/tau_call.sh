#!/usr/bin/env bash
set -euo pipefail
set +H; umask 022
Q=".tau_fifo/queue"; mkdir -p "$Q"
tool="${1:-}"; inp="${2:-}"; out="${3:-}"
[ -n "$tool" ] || { echo "[err] usage: tau_call.sh <tool> <input_path> <output_path>"; exit 2; }
json=$(printf '{"tool":"%s","input_path":"%s","output_path":"%s"}' "$tool" "$inp" "$out")
id="$(date -u +%Y%m%d-%H%M%S)-$$-$RANDOM"
req="$Q/$id.req"; res="$Q/$id.res"; outtmp=$(mktemp)
trap 'rm -f "$req" "$res" "$outtmp"' EXIT
mkfifo "$res"
printf "%s" "$json" > "$req"
( cat "$res" > "$outtmp" ) & rp=$!
timeout=${TAU_TIMEOUT:-30}; start=$(date +%s)
while kill -0 "$rp" 2>/dev/null; do now=$(date +%s); [ $((now-start)) -ge "$timeout" ] && { kill "$rp" 2>/dev/null || true; echo "[err] timeout"; exit 124; }; sleep 0.05; done
resp=$(cat "$outtmp")
printf "%s\n" "$resp"
case "$resp" in *'\"ok\":false'*) exit 10 ;; esac
