#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
find src -type f -name "*.lean" -print0 | sort -z | while IFS= read -r -d "" f; do bash scripts/meta/capsule_one.sh "$f" || true; done
