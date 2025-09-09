#!/usr/bin/env bash
set -euo pipefail

# Ensure elan/lean
if ! command -v lean >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y
  export PATH="$HOME/.elan/bin:$PATH"
  echo "$HOME/.elan/bin" >> "$GITHUB_PATH" 2>/dev/null || true
fi

scripts/ensure_deps.sh

# Compute key
KEY="$(scripts/cas_key.sh)"
echo "[key] $KEY"

# Pull cache, if any
scripts/cas_pull.sh "$KEY" || true

# Update + parallel build
lake update
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-$(nproc || echo 4)}"
JOBS="${JOBS:-$LEAN_NUM_THREADS}"
echo "[build] lake build -j $JOBS (LEAN_NUM_THREADS=$LEAN_NUM_THREADS)"
if lake build -j "$JOBS"; then
  STATUS=success
else
  STATUS=failure
fi

# Push cache on success
if [ "$STATUS" = "success" ]; then
  scripts/cas_push.sh "$KEY" || true
fi

# Always emit a receipt
scripts/emit_receipt.sh "$KEY" "$STATUS"

# Exit with the build status
[ "$STATUS" = "success" ]
