#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
if compgen -G "analysis/**/*_canon.json" > /dev/null; then
  # sanitize in chunks to keep argv short
  find analysis -type f -name "*_canon.json" -print0 | xargs -0 -n 25 python3 scripts/receipt/sanitize_json.py
fi
