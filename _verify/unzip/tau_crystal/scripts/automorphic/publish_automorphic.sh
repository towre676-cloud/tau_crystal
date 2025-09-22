#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
motive_json="${1:?supply motive json}"
[ -s .tau_ledger/manifest.json ] || printf "\n" "{"automorphic":[]}" > .tau_ledger/manifest.json
python scripts/automorphic/_publish.py "$motive_json"
