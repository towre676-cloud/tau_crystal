#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
scripts/ops/testimony_gate.sh
scripts/ops/import_guard.sh
scripts/ops/poem_guard.sh
tgt="${1:-.}"
scripts/ops/cache_attest.sh "$tgt" >/dev/null
commit=$(git rev-parse HEAD)
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
att=".tau_ledger/cache/latest.json"
out=".tau_ledger/conscience/${commit}.json"; : > "$out"
printf "%s" "{" >> "$out"
printf "%s" "\"commit\":\"$commit\",\"utc\":\"$ts\",\"attestation\":\"$(basename "$att")\"" >> "$out"
printf "%s\n" "}" >> "$out"
echo "[conscience] ok: $out"
