#!/usr/bin/env bash
set -Eeuo pipefail; set +H
REPO="${REPO:-$(gh repo view --json nameWithOwner -q .nameWithOwner)}"
Q='.[] | [ .number, ((.labels // []) | map(.name) | join(",")), .isDraft, .mergeStateStatus, .url ] | @tsv'
gh pr list -R "$REPO" --state open -L 200 --json number,isDraft,mergeStateStatus,labels,url --jq "$Q" | sort -V | awk -F'\t' -f scripts/ci/B8_roll.awk | sort -V
