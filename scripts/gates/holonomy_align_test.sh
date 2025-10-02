#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
bash scripts/gates/holonomy_align.sh cases/seifert_example.ini | tee ".tau_ledger/holonomy/run_${RANDOM}.log"
