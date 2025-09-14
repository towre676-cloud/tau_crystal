#!/usr/bin/env bash
set -Eeuo pipefail; set +H
mode="${1:-warm}"
runner_tag="${2:-local}"
start=$(date -u +%s)
if [ "$mode" = "cold" ]; then rm -rf .lake lake-packages build 2>/dev/null || true; fi
if command -v lake >/dev/null 2>&1; then
  lake update >/dev/null 2>&1 || true
  lake build
elif command -v mingw32-make >/dev/null 2>&1; then
  mingw32-make tau || mingw32-make
elif command -v make >/dev/null 2>&1; then
  make tau || make
else
  echo "[err] need lake (preferred) or make/mingw32-make on PATH" >&2; exit 3
fi
./scripts/assure.sh
end=$(date -u +%s); dur=$((end-start))
rec=$(tail -n1 receipts/CHAIN | awk "{print \$2}")
sha=$(sha256sum "$rec" | awk "{print \$1}")
ts=$(date -u +%Y-%m-%dT%H:%M:%SZ)
os=$(uname -s)
commit=$(git rev-parse --short=12 HEAD)
mlrev=$(scripts/bench/mathlib_rev.sh || echo unknown)
out=".tau_ledger/bench/runs.ndjson"; mkdir -p "$(dirname "$out")"
printf "%s" "{\"utc_iso\":\"$ts\",\"commit\":\"$commit\",\"mode\":\"$mode\",\"os\":\"$os\",\"runner\":\"$runner_tag\",\"mathlib_rev\":\"$mlrev\",\"duration_s\":$dur,\"receipt_path\":\"$rec\",\"receipt_sha256\":\"$sha\"}" >> "$out"
printf "\n" >> "$out"
echo "[bench] $mode $runner_tag $os dur=${dur}s rec=$(basename "$rec")"
