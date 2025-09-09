#!/usr/bin/env bash
set -euo pipefail
if ! command -v lean >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y
  export PATH="$HOME/.elan/bin:$PATH"
  echo "$HOME/.elan/bin" >> "$GITHUB_PATH" 2>/dev/null || true
fi
scripts/ensure_deps.sh
KEY="$(scripts/cas_key.sh)"
echo "[key] $KEY"
scripts/cas_pull.sh "$KEY" || true
lake update
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-$(nproc || echo 4)}"
JOBS="${JOBS:-$LEAN_NUM_THREADS}"
echo "[build] lake build -j $JOBS (LEAN_NUM_THREADS=$LEAN_NUM_THREADS)"
STATUS=success
lake build -j "$JOBS" || STATUS=failure
[ "$STATUS" = "success" ] && scripts/cas_push.sh "$KEY" || true
scripts/emit_receipt.sh "$KEY" "$STATUS"
[ "$STATUS" = "success" ]
