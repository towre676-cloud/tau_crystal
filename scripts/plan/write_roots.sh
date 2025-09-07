#!/usr/bin/env bash
set -euo pipefail
log(){ printf '[roots] %s\n' "$*" >&2; }

PLAN="${PLAN_OVERRIDE:-${TAU_PLAN:-FREE}}"
case "${PLAN^^}" in
  PRO)  PLAN=PRO;  REQ=true;  LAU=true;  RET=180; MAX=20 ;;
  *)    PLAN=FREE; REQ=false; LAU=false; RET=14;  MAX=2  ;;
esac

ROOTS_FILE=".tau_plan_roots.env"
{
  echo "# τ‑Crystal plan roots — committed source of truth"
  echo "TAU_PLAN=${PLAN}"
  echo "TAU_REQUIRE_PROOFS=${REQ}"
  echo "TAU_LAURENT_ENABLED=${LAU}"
  echo "TAU_RETENTION_DAYS=${RET}"
  echo "TAU_MAX_WORKERS=${MAX}"
  echo "TAU_ROOTS_COMMITTED_AT=$(date -u +'%Y-%m-%dT%H:%M:%SZ')"
  echo "TAU_ROOTS_GIT_HEAD=$(git rev-parse --short HEAD 2>/dev/null || echo 'detached')"
} > "$ROOTS_FILE"
log "wrote $ROOTS_FILE"

mkdir -p docs
MAN="docs/manifest.md"
[ -f "$MAN" ] || printf '# τ‑Crystal Manifest\n\n' > "$MAN"

tmp="$(mktemp)"
git ls-files -z | xargs -0 sha256sum | LC_ALL=C sort -k2 > "$tmp"
MERKLE_ROOT="$(sha256sum "$tmp" | awk '{print $1}')"
rm -f "$tmp"

# portable in-place sed
if grep -q '^MERKLE_ROOT:' "$MAN"; then
  if sed --version >/dev/null 2>&1; then
    sed -i -E "s|^MERKLE_ROOT:.*$|MERKLE_ROOT: ${MERKLE_ROOT}|" "$MAN"
  else
    sed -i '' -E "s|^MERKLE_ROOT:.*$|MERKLE_ROOT: ${MERKLE_ROOT}|" "$MAN"
  fi
else
  printf '\nMERKLE_ROOT: %s\n' "$MERKLE_ROOT" >> "$MAN"
fi
log "stamped MERKLE_ROOT into $MAN"

echo "TAU_PLAN=${PLAN}"
echo "TAU_REQUIRE_PROOFS=${REQ}"
echo "TAU_LAURENT_ENABLED=${LAU}"
echo "TAU_RETENTION_DAYS=${RET}"
echo "TAU_MAX_WORKERS=${MAX}"
echo "TAU_MERKLE_ROOT=${MERKLE_ROOT}"
