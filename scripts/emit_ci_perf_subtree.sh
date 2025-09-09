#!/usr/bin/env bash
set -euo pipefail
set +H

TS(){ date -u +%Y-%m-%dT%H:%M:%SZ; }
ESC(){ sed -e "s/\\/\\\\/g" -e "s/\"/\\"/g"; }
BIN(){ command -v "$1" >/dev/null 2>&1 && printf "%s" "$(command -v "$1")" || printf ""; }
BIN_SHA(){ p=$(BIN "$1"); [ -n "$p" ] && sha256sum "$p" | awk "{print \$1}" || printf ""; }

out_json=".tau_ledger/perf/manifest.json"
out_md="docs/CI_PERF.md"
mkdir -p ".tau_ledger/perf"

gitsha="$(git rev-parse --short=12 HEAD 2>/dev/null || echo unknown)"
kernel="$(uname -srmo 2>/dev/null || uname -a || true)"
glibc="$((ldd --version 2>/dev/null || true) | head -n1 | tr -s " ")"
image="${ImageVersion:-}${ImageOS:+/}${ImageOS:-}"

lean_sha="$(BIN_SHA lean)"; lake_sha="$(BIN_SHA lake)"; bash_sha="$(BIN_SHA bash)"; sum_sha="$(BIN_SHA sha256sum)"

# Collect scenarios from any prior bench JSON files (optional)
sc_tmp="$(mktemp)"; : > "$sc_tmp"
for f in .tau_ledger/ci_bench_*.json; do
  [ -f "$f" ] || continue
  # crude extractor: label|wall|rss from {"label":"...","wall":"...","rss_kb":"..."}
  grep -oE "\\{\\\"label\\\":\\\"[^\\\"]+\\\",\\\"wall\\\":\\\"[^\\\"]*\\\",\\\"rss_kb\\\":\\\"[^\\\"]*\\\"\\}" "$f" \\
   | sed -E "s/.*\\\"label\\\":\\\"([^\\\"]+)\\\",\\\"wall\\\":\\\"([^\\\"]*)\\\",\\\"rss_kb\\\":\\\"([^\\\"]*)\\\".*/\\1|\\2|\\3/" >> "$sc_tmp"
done

# Write JSON (no jq dependency)
: > "$out_json"
printf "%s" "{" >> \"$out_json\"
printf "%s" "\"timestamp\":\"$(TS)\"," >> \"$out_json\"
printf "%s" "\"git_sha\":\"$gitsha\"," >> \"$out_json\"
printf "%s" "\"runner\":{\"kernel\":\"$(printf "%s" "$kernel" | ESC)\",\"glibc\":\"$(printf "%s" "$glibc" | ESC)\",\"image\":\"$(printf "%s" "$image" | ESC)\"}," >> \"$out_json\"
printf "%s" "\"binaries\":{\"lean\":\"$lean_sha\",\"lake\":\"$lake_sha\",\"bash\":\"$bash_sha\",\"sha256sum\":\"$sum_sha\"}," >> \"$out_json\"
printf "%s" "\"scenarios\":[" >> \"$out_json\"
first=1
while IFS="|" read -r L W M; do
  [ -z "${L:-}" ] && continue
  [ $first -eq 1 ] || printf "," >> "$out_json"
  first=0
  printf "%s" "{\"label\":\"$(printf "%s" "$L" | ESC)\",\"wall\":\"$(printf "%s" "$W" | ESC)\",\"rss_kb\":\"$(printf "%s" "$M" | ESC)\"}" >> "$out_json"
done < "$sc_tmp"
printf "%s" "]}" >> "$out_json"
rm -f "$sc_tmp"

# Write Markdown summary
: > "$out_md"
printf "%s\n" "# CI Performance (τ-Crystal)" >> "$out_md"
printf "%s\n" "" >> "$out_md"
printf "%s\n" "- **Timestamp:** $(TS)" >> "$out_md"
printf "%s\n" "- **Commit:** $gitsha" >> "$out_md"
printf "%s\n" "- **Runner:** $(printf "%s" "$kernel" | ESC)" >> "$out_md"
printf "%s\n" "- **glibc:** $(printf "%s" "$glibc" | ESC)" >> "$out_md"
printf "%s\n" "" >> "$out_md"
printf "%s\n" "## Binaries (SHA-256)" >> "$out_md"
printf "%s\n" "" >> "$out_md"
printf "%s\n" "| binary | sha256 |" >> "$out_md"
printf "%s\n" "|---|---|" >> "$out_md"
printf "%s\n" "| lean | ${lean_sha:-} |" >> "$out_md"
printf "%s\n" "| lake | ${lake_sha:-} |" >> "$out_md"
printf "%s\n" "| bash | ${bash_sha:-} |" >> "$out_md"
printf "%s\n" "| sha256sum | ${sum_sha:-} |" >> "$out_md"
printf "%s\n" "" >> "$out_md"
printf "%s\n" "## Scenarios" >> "$out_md"
printf "%s\n" "" >> "$out_md"
printf "%s\n" "| label | wall | rss_kb |" >> "$out_md"
printf "%s\n" "|---|---|---|" >> "$out_md"
has_row=0
if grep -q . "$sc_tmp" 2>/dev/null; then :; fi
for f in .tau_ledger/ci_bench_*.json; do [ -f "$f" ] || continue; 
  grep -oE "\\{\\\"label\\\":\\\"[^\\\"]+\\\",\\\"wall\\\":\\\"[^\\\"]*\\\",\\\"rss_kb\\\":\\\"[^\\\"]*\\\"\\}" "$f" \\
   | sed -E "s/.*\\\"label\\\":\\\"([^\\\"]+)\\\",\\\"wall\\\":\\\"([^\\\"]*)\\\",\\\"rss_kb\\\":\\\"([^\\\"]*)\\\".*/| \\1 | \\2 | \\3 |/" >> "$out_md"; has_row=1; done
if [ "${has_row:-0}" -eq 0 ]; then printf "%s\n" "| (none) |  |  |" >> "$out_md"; fi

echo "[ok] wrote $out_json and $out_md"
