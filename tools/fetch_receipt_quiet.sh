#!/usr/bin/env bash
# Quiet fetch of latest *completed* run's receipt for a workflow
set -euo pipefail
BR="${1:-$(git rev-parse --abbrev-ref HEAD)}"
WF="${2:-.github/workflows/three-streams.yml}"

export GH_PAGER=cat PAGER=cat GIT_PAGER=cat LESS=FRX

RID="$(gh run list --workflow "$WF" --branch "$BR" --status completed -L 1 \
  --json databaseId --jq '.[0].databaseId' 2>/dev/null || true)"

if [ -z "${RID:-}" ]; then
  echo "[err] no completed run yet for $WF on $BR"
  return 1 2>/dev/null || exit 1
fi

if [ "${WAIT:-0}" = "1" ]; then
  while :; do
    S="$(gh run view "$RID" --json status --jq .status 2>/dev/null || echo)"
    [ "$S" = "completed" ] && break
    sleep 2
  done
fi

rm -rf .artifact_tmp && mkdir -p .artifact_tmp
if gh run download "$RID" -n smartcache-receipt -D .artifact_tmp >/dev/null 2>&1; then
  [ -s .artifact_tmp/receipt.json ] && { echo "[ok] .artifact_tmp/receipt.json"; exit 0; }
  echo "[err] artifact missing receipt.json"; return 3 2>/dev/null || exit 3
else
  echo "[err] download failed for run $RID"; return 2 2>/dev/null || exit 2
fi
