#!/usr/bin/env bash
set -euo pipefail
export GH_PAGER=cat PAGER=cat GIT_PAGER=cat LESS=FRX
BRANCH="${1:-$(git rev-parse --abbrev-ref HEAD)}"
WF="${2:-.github/workflows/lean-remote-cache.yml}"
RID="$(gh run list --workflow "$WF" --branch "$BRANCH" -L 1 --json databaseId \
  --template '{{- if gt (len .) 0 -}}{{printf "%.0f" (index . 0).databaseId}}{{end -}}' 2>/dev/null || true)"
[ -n "$RID" ] || { echo "[err] no runs yet for $WF on $BRANCH"; exit 1; }
if [ "${WAIT:-0}" = "1" ]; then gh run watch "$RID" >/dev/null || true; fi
rm -rf .artifact_tmp && mkdir -p .artifact_tmp
if ! gh run download "$RID" --name smartcache-receipt -D .artifact_tmp; then
  echo "[err] no smartcache-receipt; dumping logs:"
  gh run view "$RID" --log-failed || gh run view "$RID" --log
  exit 2
fi
echo "[ok] downloaded: $(find .artifact_tmp -type f -name receipt.json | head -n1)"
