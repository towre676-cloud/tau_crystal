#!/usr/bin/env bash
set -Eeuo pipefail; set +H
manifest="${1:?}"
fail="${2:-true}"
s="$(scripts/tau_verify.sh "$manifest")"
echo "status=$s" >> "${GITHUB_OUTPUT:-/dev/null}" 2>/dev/null || true
echo "::notice::tau-crystal status: $s"
if [ "$fail" = "true" ] && [ "$s" != "ok" ]; then echo "::error::verification failed ($s)"; exit 1; fi
