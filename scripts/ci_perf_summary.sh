#!/usr/bin/env bash
set -euo pipefail
set +H
f=".tau_ledger/perf/manifest.json"
[ -f "$f" ] || { echo "[err] no manifest: $f"; exit 1; }
ts=$(grep -oE "\"timestamp\":\"[^\"]+\"" "$f" | head -n1 | sed -E "s/.*:\"([^\"]+)\".*/\\1/")
sha=$(grep -oE "\"git_sha\":\"[^\"]+\"" "$f" | head -n1 | sed -E "s/.*:\"([^\"]+)\".*/\\1/")
kern=$(grep -oE "\"kernel\":\"[^\"]+\"" "$f" | head -n1 | sed -E "s/.*:\"([^\"]+)\".*/\\1/")
glibc=$(grep -oE "\"glibc\":\"[^\"]+\"" "$f" | head -n1 | sed -E "s/.*:\"([^\"]+)\".*/\\1/")
echo "runner: $kern | $glibc"
printf "%-14s %-10s %-10s\n" "scenario" "wall" "rss_kb"
grep -oE "\\{\\\"label\\\":\\\"[^\\\"]+\\\",\\\"wall\\\":\\\"[^\\\"]*\\\",\\\"rss_kb\\\":\\\"[^\\\"]*\\\"\\}" "$f" \\
 | sed -E "s/.*\\\"label\\\":\\\"([^\\\"]+)\\\",\\\"wall\\\":\\\"([^\\\"]*)\\\",\\\"rss_kb\\\":\\\"([^\\\"]*)\\\".*/\\1 \\2 \\3/" \\
 | while read -r L W M; do printf "%-14s %-10s %-10s\n" "$L" "$W" "${M:-}"; done
