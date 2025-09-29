#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
BASE=".tau_ledger/lean_module_capsules"; IDX="$BASE/index.json"; SHA="$BASE/index.sha256"
[ -s "$IDX" ] || { echo "[err] missing $IDX"; exit 2; }
root=$(cut -d" " -f1 "$SHA" 2>/dev/null || true); [ -n "${root:-}" ] || root="UNSEALED"
tc=$(lake env lean --version 2>/dev/null | head -n1 || echo "lean:unknown")
lv=$(lake --version 2>/dev/null | head -n1 || echo "lake:unknown")
tot=$(find "$BASE" -type f -name "*.json" ! -name "index.json" ! -name "capsule_set.seal.json" | awk "END{print NR}")
ok=$(grep -o "\"build_ok\"[[:space:]]*:[[:space:]]*1" "$IDX" | awk "END{print NR}")
bad=$(grep -o "\"build_ok\"[[:space:]]*:[[:space:]]*0" "$IDX" | awk "END{print NR}")
now=$(date -u +%Y-%m-%dT%H:%M:%SZ)
out="$BASE/capsule_set.seal.json"; : > "$out"
printf "{" >> "$out"
printf "\"kind\":\"lean.module.capsule.set\"," >> "$out"
printf "\"root_hash\":\"%s\"," "$root" >> "$out"
printf "\"sealed_at\":\"%s\"," "$now" >> "$out"
printf "\"toolchain\":\"%s\"," "$tc" >> "$out"
printf "\"lake\":\"%s\"," "$lv" >> "$out"
printf "\"total_modules\":%s," "$tot" >> "$out"
printf "\"build_ok\":%s," "$ok" >> "$out"
printf "\"build_fail\":%s," "$bad" >> "$out"
printf "\"index_path\":\"%s\"" "$IDX" >> "$out"
printf "}\n" >> "$out"
