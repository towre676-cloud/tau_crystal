#!/usr/bin/env bash
set -e
BRANCH="${1:-$(git rev-parse --abbrev-ref HEAD)}"
WF=".github/workflows/smart-ci.yml"
RID="$(gh run list --workflow "$WF" --branch "$BRANCH" --limit 1 --json databaseId --jq 
'.[0].databaseId' 2>/dev/null || true)"
if [ -z "$RID" ]; then
fi
[ -n "$RID" ] || { echo "[err] No smart-ci runs yet on $BRANCH"; exit 1; }
if [ "${WAIT:-0}" = "1" ]; then gh run watch "$RID" >/dev/null || true; fi
rm -rf .artifact_tmp && mkdir -p .artifact_tmp
if ! gh run download "$RID" --name smartcache-receipt -D .artifact_tmp; then
  if ! gh run download "$RID" -D .artifact_tmp; then
    echo "[err] no artifacts; logs:"
    gh run view "$RID" --log-failed || gh run view "$RID" --log; exit 2
  fi
fi
REC="$(find .artifact_tmp -type f -name "receipt*.json" -o -name "receipt.json" | head -n1)"
[ -s "$REC" ] || { echo "[err] no receipt.json found in artifacts"; exit 3; }
echo "[ok] downloaded: $REC"
