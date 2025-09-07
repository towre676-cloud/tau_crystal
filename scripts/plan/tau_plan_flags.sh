#!/usr/bin/env bash
# tau_plan_flags.sh — zero-dependency, never-crash plan flags
# Usage:
#   PLAN_OVERRIDE=PRO bash scripts/plan/tau_plan_flags.sh >> "$GITHUB_ENV"
# or:
#   eval "$(
#     PLAN_OVERRIDE=PRO bash scripts/plan/tau_plan_flags.sh
#   )"

set -u
trap 'printf "[tau_plan_flags] soft-exit (%s:%s)\n" "${BASH_SOURCE[0]##*/}" "$LINENO" >&2' ERR

# Accept FREE (default) or PRO from env. Anything else → FREE.
PLAN="${PLAN_OVERRIDE:-FREE}"
case "${PLAN^^}" in
  PRO)  PLAN="PRO"  ;;
  *)    PLAN="FREE" ;;
esac

if [ "$PLAN" = "PRO" ]; then
  TAU_REQUIRE_PROOFS=true
  TAU_LAURENT_ENABLED=true
  TAU_RETENTION_DAYS=180
  TAU_MAX_WORKERS=20
else
  TAU_REQUIRE_PROOFS=false
  TAU_LAURENT_ENABLED=false
  TAU_RETENTION_DAYS=14
  TAU_MAX_WORKERS=2
fi

# Print in both styles: key=value (for eval) and GHA-compatible "name=value"
printf 'TAU_PLAN=%s\n'           "$PLAN"
printf 'TAU_REQUIRE_PROOFS=%s\n' "$TAU_REQUIRE_PROOFS"
printf 'TAU_LAURENT_ENABLED=%s\n' "$TAU_LAURENT_ENABLED"
printf 'TAU_RETENTION_DAYS=%s\n' "$TAU_RETENTION_DAYS"
printf 'TAU_MAX_WORKERS=%s\n'    "$TAU_MAX_WORKERS"

# If running inside GitHub Actions, emit to $GITHUB_ENV when available.
if [ -n "${GITHUB_ENV:-}" ] && [ -w "${GITHUB_ENV:-/dev/null}" ]; then
  {
    echo "TAU_PLAN=$PLAN"
    echo "TAU_REQUIRE_PROOFS=$TAU_REQUIRE_PROOFS"
    echo "TAU_LAURENT_ENABLED=$TAU_LAURENT_ENABLED"
    echo "TAU_RETENTION_DAYS=$TAU_RETENTION_DAYS"
    echo "TAU_MAX_WORKERS=$TAU_MAX_WORKERS"
  } >> "$GITHUB_ENV" || true
fi

exit 0
