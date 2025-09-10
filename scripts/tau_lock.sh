#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/_tau_common.sh"
ensure jq
CONTRACT="${1:-protocol/example.contract.json}"
[ -f "$CONTRACT" ] || { echo "no contract: $CONTRACT" >&2; exit 2; }
CSHA="$(sha256f "$CONTRACT")"
printf "{\"type\":\"lock\",\"ts\":\"%s\",\"data\":{\"contract_sha256\":\"%s\",\"contract_path\":\"%s\"}}\n" "$(ts)" "$CSHA" "$CONTRACT" >> "$TRACE"
echo "$CSHA"
