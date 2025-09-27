#!/usr/bin/env bash
set -euo pipefail
scripts/gates/holonomy_align.sh scripts/ops/holonomy_example.ini | tee .cache/holonomy_example.json
