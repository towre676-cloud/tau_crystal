#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../../.."/lean/HEO
lake build
