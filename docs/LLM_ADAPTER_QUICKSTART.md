## LLM Adapter quickstart

Prereqs: bash, openssl, shasum (or certutil), jq

1) Lock:  scripts/tau_lock.sh protocol/example.contract.json
2) Step:  scripts/tau_step.sh "llm:proposer" protocol/example.contract.json .tmp/step1.out.json
3) Seal:  scripts/tau_commit.sh
4) Show:  scripts/tau_status.sh
