#!/usr/bin/env bash
set -euo pipefail
export GH_PAGER=cat PAGER=cat GIT_PAGER=cat LESS=FRX

BRANCH="${1:-$(git rev-parse --abbrev-ref HEAD)}"
WF_PATH=".github/workflows/smart-ci.yml"

# Use --json/--jq so the ID is not rendered in scientific notation
RID="$(gh run list --workflow "$WF_PATH" --branch "$BRANCH" -L 1 \
       --json databaseId --jq '.[0].databaseId' 2>/dev/null || true)"

# Fallback: newest run whose workflowName == "smart-ci"
if [ -z "${RID:-}" ]; then
  RID="$(gh run list --branch "$BRANCH" -L 10 \
         --json databaseId,workflowName \
         --jq 'map(select(.workflowName=="smart-ci")) | (.[0].databaseId // "")' \
         2>/dev/null || true)"
fi

[ -n "${RID:-}" ] || { echo "[err] no smart-ci runs yet on $BRANCH"; exit 1; }

# Optional: WAIT=1 ./tools/verify_last_receipt.sh
if [ "${WAIT:-0}" = "1" ]; then gh run watch "$RID" >/dev/null || true; fi

rm -rf .artifact_tmp && mkdir -p .artifact_tmp

# Try the named artifact first, then any artifacts on the run
if ! gh run download "$RID" --name smartcache-receipt -D .artifact_tmp 2>/dev/null; then
  if ! gh run download "$RID" -D .artifact_tmp; then
    echo "[err] no artifacts on run $RID; dumping logs:"
    gh run view "$RID" --log-failed || gh run view "$RID" --log
    exit 2
  fi
fi

REC="$(find .artifact_tmp -type f -name 'receipt.json' | head -n1 || true)"
[ -s "${REC:-}" ] || { echo "[err] no receipt.json in artifacts"; exit 3; }

echo "[ok] downloaded: $REC"
