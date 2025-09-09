#!/usr/bin/env bash
set -euo pipefail
export GH_PAGER=cat PAGER=cat GIT_PAGER=cat LESS=FRX
BRANCH="${1:-$(git rev-parse --abbrev-ref HEAD)}"
WF="${2:-.github/workflows/lean-remote-cache.yml}"

pick_run() {
  gh run list --workflow "$WF" --branch "$BRANCH" -L 5 --json databaseId \
    --template '{{- range . -}}{{printf "%.0f\n" .databaseId}}{{end -}}' 2>/dev/null | head -n1
}
RID="$(pick_run || true)"
[ -n "${RID:-}" ] || { echo "[err] no runs yet for $WF on $BRANCH"; exit 1; }
[ "${WAIT:-0}" = "1" ] && gh run watch "$RID" >/dev/null || true
rm -rf .artifact_tmp && mkdir -p .artifact_tmp
if ! gh run download "$RID" --name smartcache-receipt -D .artifact_tmp; then
  echo "[err] artifact missing; log follows:"; gh run view "$RID" --log-failed || gh run view "$RID" --log; exit 2
fi
REC="$(find .artifact_tmp -type f -name receipt.json | head -n1)"
[ -s "$REC" ] || { echo "[err] downloaded but no receipt.json"; exit 3; }
echo "[ok] downloaded: $REC"
