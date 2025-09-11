#!/usr/bin/env bash
set -Eeuo pipefail; set +H
manifest="${1:?}"
fail="${2:-true}"
s="$(scripts/tau_verify.sh "$manifest")"
if [ -n "${GITHUB_OUTPUT:-}" ]; then echo "status=$s" >> "$GITHUB_OUTPUT"; fi
echo "::notice::tau-crystal status: $s"
if [ "$fail" = "true" ] && [ "$s" != "ok" ]; then echo "::error::verification failed ($s)"; exit 1; fi
