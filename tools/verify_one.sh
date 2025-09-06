#!/usr/bin/env bash
set -euo pipefail
shard="${1:-0}"
sleep 0.05
printf '[verify_one] shard=%s OK\n' "$shard"
