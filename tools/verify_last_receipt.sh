#!/usr/bin/env bash
set -euo pipefail

branch="${1:-$(git rev-parse --abbrev-ref HEAD)}"
wf_candidates=("smart-ci" ".github/workflows/smart-ci.yml" "lean-minicache" ".github/workflows/lean-minicache.yml")

run_id=""
for wf in "${wf_candidates[@]}"; do
  if id=$(gh run list --workflow "$wf" --branch "$branch" --limit 1 --json databaseId -q '.[0].databaseId' 2>/dev/null); then
    if [ -n "${id:-}" ]; then run_id="$id"; break; fi
  fi
done

# Fallback: newest run on this branch (any workflow)
if [ -z "${run_id:-}" ]; then
  run_id="$(gh run list --branch "$branch" --limit 1 --json databaseId -q '.[0].databaseId' 2>/dev/null || true)"
fi

if [ -z "${run_id:-}" ]; then
  echo "[err] No GitHub Actions runs found for branch: $branch"
  echo "      Tip: push a tiny change to trigger the workflow, then re-run this script."
  exit 1
fi

# Optionally wait until the run is finished: set WAIT=1 ./tools/verify_last_receipt.sh
if [ "${WAIT:-0}" = "1" ]; then
  gh run watch "$run_id" --interval 5 || true
fi

# Try to download the expected artifact
rm -rf .tau_ledger/receipt.json .artifact_tmp 2>/dev/null || true
mkdir -p .tau_ledger .artifact_tmp

if gh run download "$run_id" --name smartcache-receipt -D .artifact_tmp >/dev/null 2>&1; then
  :
else
  echo "[warn] 'smartcache-receipt' not found on this run. Listing artifacts:"
  gh run view "$run_id" --json artifacts -q '.artifacts[].name' || true
  echo "[err] Could not find the receipt artifact on run $run_id"
  exit 2
fi

# Move and verify
mv .artifact_tmp/receipt.json .tau_ledger/receipt.json 2>/dev/null || {
  # Some GH zip names include the file path; find it
  found="$(ls -1 .artifact_tmp/**/receipt.json 2>/dev/null | head -n1 || true)"
  [ -n "$found" ] && cp "$found" .tau_ledger/receipt.json
}
rm -rf .artifact_tmp

if [ ! -s .tau_ledger/receipt.json ]; then
  echo "[err] Downloaded artifact but couldn't find receipt.json"
  exit 3
fi

python3 scripts/manifest_verify.py
