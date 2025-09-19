#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
git add -A; git commit -m "snapshot: $(date -u +%Y-%m-%dT%H:%M:%SZ)" || true
BR="$(git rev-parse --abbrev-ref HEAD)"; git fetch origin "$BR" >/dev/null 2>&1 || true
git pull --rebase origin "$BR" || true; git push -u origin "$BR"
