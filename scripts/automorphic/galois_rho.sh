#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
in_json="${1:?supply hecke json path}"
python scripts/automorphic/galois_rho.py "$in_json"
