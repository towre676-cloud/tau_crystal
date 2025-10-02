#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
BASE=".tau_ledger/lean_module_capsules"; OUT="docs/modules/index.html"; : > "$OUT"
printf "%s\n" "<!doctype html><meta charset=utf-8><title>Lean Module Capsules</title>" >> "$OUT"
printf "%s\n" "<h1>Lean Module Capsules</h1><p>Sealed per-module build receipts.</p><table border=1 cellpadding=6 cellspacing=0><tr><th>Module</th><th>Build</th><th>ms</th><th>src bytes</th><th>olean bytes</th><th>sealed</th></tr>" >> "$OUT"
find "$BASE" -type f -name "*.json" ! -name "index.json" ! -name "capsule_set.seal.json" -print0 | sort -z | while IFS= read -r -d "" j; do
  if ! grep -q "\"module\":" "$j"; then continue; fi
  mod=$(grep -m1 "\"module\":" "$j" | sed -E "s/.*\"module\":\"([^\"]+)\".*/\\1/")
  ok=$(grep -m1 "\"build_ok\":" "$j" | sed -E "s/.*\"build_ok\":([0-9]+).*/\\1/")
  ms=$(grep -m1 "\"build_time_ms\":" "$j" | sed -E "s/.*\"build_time_ms\":([0-9]+).*/\\1/")
  sb=$(grep -m1 "\"src_bytes\":" "$j" | sed -E "s/.*\"src_bytes\":([0-9]+).*/\\1/")
  ob=$(grep -m1 "\"olean_bytes\":" "$j" | sed -E "s/.*\"olean_bytes\":([0-9]+).*/\\1/")
  ts=$(grep -m1 "\"run_utc\":" "$j" | sed -E "s/.*\"run_utc\":\"([^\"]+)\".*/\\1/")
  badge="OK"; [ "$ok" = "1" ] || badge="FAIL"
  printf "%s\n" "<tr><td>${mod}</td><td>${badge}</td><td>${ms}</td><td>${sb}</td><td>${ob}</td><td>${ts}</td></tr>" >> "$OUT"
done
printf "%s\n" "</table>" >> "$OUT"
