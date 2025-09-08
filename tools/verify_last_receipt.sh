#!/usr/bin/env bash
set -euo pipefail
branch="${1:-$(git rev-parse --abbrev-ref HEAD)}"
wf_candidates=("smart-ci" ".github/workflows/smart-ci.yml" "lean-minicache" ".github/workflows/lean-minicache.yml")
run_id=""
for wf in "${wf_candidates[@]}"; do
  id=$(gh run list --workflow "$wf" --branch "$branch" --limit 1 --json databaseId -q ".[0].databaseId" 2>/dev/null || true)
  [ -n "${id:-}" ] && run_id="$id" && break
done
if [ -z "${run_id:-}" ]; then
  run_id="$(gh run list --branch "$branch" --limit 1 --json databaseId -q ".[0].databaseId" 2>/dev/null || true)"
fi
if [ -z "${run_id:-}" ]; then echo "[err] No runs yet for branch $branch"; exit 1; fi
rm -rf .artifact_tmp .tau_ledger/receipt.json 2>/dev/null || true
mkdir -p .artifact_tmp .tau_ledger
if gh run download "$run_id" --name smartcache-receipt -D .artifact_tmp >/dev/null 2>&1; then
  : 
else
  echo "[err] receipt artifact not found on this run. Re-run later or check job logs."
  exit 2
fi
f="$(ls -1 .artifact_tmp/**/receipt.json .artifact_tmp/receipt.json 2>/dev/null | head -n1 || true)"
[ -n "$f" ] || { echo "[err] downloaded artifact but no receipt.json inside"; exit 3; }
cp "$f" .tau_ledger/receipt.json
rm -rf .artifact_tmp
python3 scripts/manifest_verify.py
