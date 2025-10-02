#!/usr/bin/env bash
set -eu; set +H; umask 022; export LC_ALL=C LANG=C
cd "$(git rev-parse --show-toplevel 2>/dev/null || pwd)" || exit 1
canon="canon.json"; status=".tau_ledger/corridor_status.json"; : > "$status"
ok_overall=1
printf "%s\n" "{" >> "$status"
printf "%s" "  \"capsule_statuses\": [" >> "$status"
comma=""
if command -v jq >/dev/null 2>&1 && [ -f "$canon" ]; then
  mapfile -t rows < <(jq -c ".capsules[]" "$canon")
else
  rows=( "{\"capsule_name\":\"Z_runtime_capsule_v1\",\"entrypoint\":\"src/Z/ZRuntime.lean\"}" \\
         "{\"capsule_name\":\"entropy_capsule_v1\",\"entrypoint\":\".tau_ledger/atlas/atlas.json\"}" \\
         "{\"capsule_name\":\"cohomology_capsule_v1\",\"entrypoint\":\".tau_ledger/drift/drift.json\"}" )
fi
for row in "${rows[@]}"; do
  name=$(printf "%s" "$row" | sed -nE 's/.*"capsule_name":"([^"]+)".*/\1/p')
  entry=$(printf "%s" "$row" | sed -nE 's/.*"entrypoint":"([^"]+)".*/\1/p')
  present=false; [ -e "$entry" ] && present=true || ok_overall=0
  printf "%s" "$comma" >> "$status"
  printf "%s\n" "{\"name\":\"$name\",\"entrypoint\":\"$entry\",\"present\":$present}" >> "$status"
  comma=","
done
printf "%s\n" "]," >> "$status"
printf "%s\n" "  \"ok\": $ok_overall" >> "$status"
printf "%s\n" "}" >> "$status"
[ "$ok_overall" -eq 1 ] && echo "[ok] corridor verify passed" || { echo "[warn] corridor verify found missing entries"; exit 0; }
