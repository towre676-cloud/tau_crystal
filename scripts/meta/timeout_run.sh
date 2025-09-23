#!/usr/bin/env bash
# usage: timeout_run.sh <timeout-seconds> <cmd...>
set -euo pipefail; umask 022
t="${1:?seconds}"; shift
if command -v timeout >/dev/null 2>&1; then
  timeout --preserve-status "${t}s" "$@"
  exit $?
fi
# watchdog fallback
outpid=""
( "$@" ) & outpid=$!
deadline=$(( $(date +%s) + t ))
while kill -0 "$outpid" 2>/dev/null; do
  now=$(date +%s)
  if [ "$now" -ge "$deadline" ]; then
    kill -TERM "$outpid" 2>/dev/null || true
    sleep 1
    kill -KILL "$outpid" 2>/dev/null || true
    echo "[TIMEOUT] $* after ${t}s" 1>&2
    exit 124
  fi
  sleep 1
done
wait "$outpid"; exit $?
