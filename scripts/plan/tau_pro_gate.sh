#!/usr/bin/env bash
set -euo pipefail
emit(){ printf '%s=%s\n' "$1" "$2"; }
case "${PLAN_OVERRIDE:-FREE}" in
  PRO|pro) PLAN=PRO;  REQ=true;  LAU=true;  RET=180; MAX=20 ;;
  *)       PLAN=FREE; REQ=false; LAU=false; RET=14;  MAX=2  ;;
esac
emit TAU_PLAN "$PLAN"
emit TAU_REQUIRE_PROOFS "$REQ"
emit TAU_LAURENT_ENABLED "$LAU"
emit TAU_RETENTION_DAYS "$RET"
emit TAU_MAX_WORKERS "$MAX"
if [ -n "${GITHUB_ENV:-}" ] && [ -w "${GITHUB_ENV:-/dev/null}" ]; then
  {
    echo "TAU_PLAN=$PLAN"
    echo "TAU_REQUIRE_PROOFS=$REQ"
    echo "TAU_LAURENT_ENABLED=$LAU"
    echo "TAU_RETENTION_DAYS=$RET"
    echo "TAU_MAX_WORKERS=$MAX"
  } >> "$GITHUB_ENV" || true
fi
