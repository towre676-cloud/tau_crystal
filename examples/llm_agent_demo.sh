#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

# lock priors
if scripts/tau_lock.sh protocol/example.contract.json >/dev/null; then
  echo "[lock] ok"
else
  echo "[lock] fail" >&2; exit 1
fi

mkdir -p .tmp
echo '{"f":"a*x^p + b*y^q + c","params":{"a":1,"b":1,"c":0,"p":0.5,"q":0.5}}' > .tmp/step1.out.json

# record step with input/output
scripts/tau_step.sh "llm:formula-proposer" protocol/example.contract.json .tmp/step1.out.json >/dev/null

# seal and show status
scripts/tau_commit.sh
scripts/tau_status.sh
