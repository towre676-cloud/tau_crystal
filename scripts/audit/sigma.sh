#!/usr/bin/env bash
set -e; set +H; umask 022
if [ -x scripts/tools/py.sh ] && (command -v python3 >/dev/null 2>&1 || command -v py >/dev/null 2>&1 || command -v python >/dev/null 2>&1); then
  scripts/tools/py.sh scripts/sigma/check_sigma.py >/dev/null || true
fi
cat artifacts/sigma/sigma_laws.json
