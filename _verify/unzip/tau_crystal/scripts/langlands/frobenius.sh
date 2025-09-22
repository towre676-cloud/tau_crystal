#!/usr/bin/env bash
set -Eeuo pipefail; set +H
place="${1:-global}"
u="${GITHUB_RUN_ID:-0}.${GITHUB_SHA:-0}.${RANDOM}"
ram=1; [ -n "${CI:-}" ] && ram=$((ram+1)); [ -n "${GITHUB_ACTIONS:-}" ] && ram=$((ram+1))
hash(){ if command -v sha256sum >/dev/null 2>&1; then printf "%s" "$1" | sha256sum | cut -d" " -f1; elif command -v shasum >/dev/null 2>&1; then printf "%s" "$1" | shasum -a 256 | cut -d" " -f1; else printf "%s" "$1" | openssl dgst -sha256 | awk "{print \$2}"; fi; }
h=$(hash "$place|$u|$ram")
printf "%s\t%s\t%s\t%s\n" "$place" "$u" "$ram" "$h"
