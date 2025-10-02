#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."/lean/HEO
# ensure Lake is available (installed by elan action in CI)
lake build
