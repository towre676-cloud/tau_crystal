#!/usr/bin/env bash
set -Eeuo pipefail; set +H
command -v lake >/dev/null 2>&1 && exit 0
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
command -v lake >/dev/null 2>&1 || true
