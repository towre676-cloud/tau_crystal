#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
python scripts/automorphic/zero_critical.py
