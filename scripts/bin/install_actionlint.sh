#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
ver="${1:-latest}"
dir="${2:-$HOME/.local/bin}"
mkdir -p "$dir"
url=https://raw.githubusercontent.com/rhysd/actionlint/main/scripts/download-actionlint.bash
curl -sSfL "$url" | bash -s -- "$ver" "$dir"
printf "%s\n" "$dir" >> "$GITHUB_PATH" 2>/dev/null || true
