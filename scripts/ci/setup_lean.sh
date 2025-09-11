#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
export PATH="$HOME/.elan/bin:$PATH"
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
echo "$HOME/.elan/bin" >> "$GITHUB_PATH" 2>/dev/null || true
elan --version || true
lake --version || true
lake update
