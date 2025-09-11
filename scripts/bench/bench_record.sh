#!/usr/bin/env bash
set -u; set +e; set +H
mode="${1:-warm}"  # warm|cold
runner_tag="${2:-local}"
start=$(date -u +%s)
if [ "$mode" = "cold" ]; then rm -rf .lake lake-packages build 2>/dev/null || :; fi
if command -v lake >/dev/null 2>&1; then
  if [ "$mode" = "cold" ]; then lake update >/dev/null 2>&1 || :; fi
  lake build || :
elif command -v mingw32-make >/dev/null 2>&1; then
  mingw32-make tau || mingw32-make || :
elif command -v make >/dev/null 2>&1; then
  make tau || make || :
else
  echo "[warn] no lake/make on PATH; skipping build"
fi
if [ -z "${TAU_NO_ASSURE:-}" ]; then ./scripts/assure.bench.sh || :; fi || :
end=$(date -u +%s); dur=$((end-start))
rec=$(awk 'match($0,/^([0-9a-f]{64})[[:space:]]+(.+)$/,a){p=a[2]} END{if(p) print p}' receipts/CHAIN 2>/dev/null | tr -d '')
sha=""; [ -n "$rec" ] && sha=$(sha256sum "$rec" | awk '{print $1}')
sha=""; [ -n "$rec" ] && sha=$(sha256sum "$rec" | awk "{print \$1}")
ts=$(date -u +%Y-%m-%dT%H:%M:%SZ)
os=$(uname -s)
commit=$(git rev-parse --short=12 HEAD 2>/dev/null || echo "unknown")
mlrev=$(scripts/bench/mathlib_rev.sh 2>/dev/null || echo unknown)
out=".tau_ledger/bench/runs.ndjson"; mkdir -p "$(dirname "$out")"
printf "%s\n" "{\"utc_iso\":\"$ts\",\"commit\":\"$commit\",\"mode\":\"$mode\",\"os\":\"$os\",\"runner\":\"$runner_tag\",\"mathlib_rev\":\"$mlrev\",\"duration_s\":$dur,\"receipt_path\":\"$rec\",\"receipt_sha256\":\"$sha\"}" >> "$out"
echo "[bench] $mode $runner_tag $os dur=${dur}s rec=$(basename "$rec")"
