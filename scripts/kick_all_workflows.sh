#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
BRANCH="${1:-main}"
tmp="$(mktemp -t kickwf.XXXXXX.tsv)"; trap 'rm -f "$tmp"' EXIT
printf "🔁 Triggering ALL workflows on branch: %s\n\n" "$BRANCH"
gh workflow list --limit 500 --json id,name,path,state | jq -r .[] | [.id,.name,.path] | @tsv > "$tmp"
[ -s "$tmp" ] || { echo "no workflows found"; exit 0; }
while IFS=$'\t' read -r WF_ID WF_NAME WF_PATH; do
  [ -n "$WF_ID" ] || continue
  printf "▶ %s  (%s)\n" "$WF_NAME" "$WF_PATH"
  if gh workflow run "$WF_PATH" --ref "$BRANCH" >/dev/null 2>&1; then
    echo "   dispatched via workflow_dispatch"
    continue
  fi
  LAST_RUN_ID="$(gh run list --workflow "$WF_PATH" --branch "$BRANCH" --json databaseId -q .[0].databaseId 2>/dev/null || true)"
  if [ -n "$LAST_RUN_ID" ]; then
    if gh run rerun "$LAST_RUN_ID" >/dev/null 2>&1; then
      echo "   rerun requested for latest run: $LAST_RUN_ID"
    else
      echo "   could not rerun last run ($LAST_RUN_ID) — skipped"
    fi
  else
    echo "   no prior run and no dispatch event — skipped"
  fi
done < "$tmp"
exit 0
