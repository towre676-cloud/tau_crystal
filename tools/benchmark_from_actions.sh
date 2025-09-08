#!/usr/bin/env bash
set -euo pipefail
have(){ command -v "$1" >/dev/null 2>&1; }
if ! have gh; then echo "[err] GitHub CLI (gh) not found"; exit 1; fi
DEFAULT=$(git remote show origin 2>/dev/null | sed -n "s/.*HEAD branch: //p"); DEFAULT=${DEFAULT:-main}
WFID=$(gh workflow list --json name,id,path -q ".[] | select(.path==\".github/workflows/smart-ci.yml\") | .id" | head -n1)
if [ -z "${WFID:-}" ]; then echo "[err] smart-ci workflow not found"; exit 2; fi
fresh_ms=$(gh run list --workflow "$WFID" --branch "$DEFAULT" --status success --limit 1 --json durationMS -q ".[0].durationMS" 2>/dev/null || true)
hit_ms=$(gh run list --workflow "$WFID" --status success --limit 1 --json headBranch,durationMS -q "[.[] | select(.headBranch|startswith(\"demo/cache-hit-\"))][0].durationMS" 2>/dev/null || true)
fresh_s=$(( ${fresh_ms:-0} / 1000 ))
hit_s=$(( ${hit_ms:-0} / 1000 ))
mkdir -p docs
OUT="docs/BENCHMARK.md"; : > "$OUT"
printf "%s\\n" "# SmartCache Benchmark (automated)" >> "$OUT"
printf "%s\\n" "" >> "$OUT"
printf "%s\\n" "| Scenario | Duration |" >> "$OUT"
if [ "$hit_s" -gt 0 ]; then printf "%s\\n" "| Hydrated build (cache hit) | ${hit_s}s |" >> "$OUT"; else printf "%s\\n" "| Hydrated build (cache hit) | (pending) |" >> "$OUT"; fi
echo "[ok] wrote $OUT";
