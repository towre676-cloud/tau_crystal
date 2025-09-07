#!/usr/bin/env bash
set -euo pipefail
repo="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$repo"

# 1) your existing assure
rpath="$(scripts/assure.sh)"

# 2) emit boundary census
census="$(scripts/boundary_census.sh)"

# 3) staple: copy alongside receipt
rc_dir="$(dirname "$rpath")"
cp "$census" "$rc_dir/$(basename "$census")"

echo "$rpath"
