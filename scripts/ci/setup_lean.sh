#!/usr/bin/env bash
set -Eeuo pipefail; set +H
if command -v lean >/dev/null 2>&1; then exit 0; fi
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
echo "$HOME/.elan/bin" >> "$GITHUB_PATH" 2>/dev/null || true
