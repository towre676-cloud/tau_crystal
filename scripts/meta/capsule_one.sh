#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
. scripts/meta/_capsule_common.sh
BASE=".tau_ledger/lean_module_capsules"; TMP=".cache/capsules"; mkdir -p "$BASE" "$TMP" exe/.capsule_each
rel="$1"; [ -f "$rel" ] || { echo "[err] missing: $rel"; exit 2; }
case "$rel" in ./*) rel="${rel#./}";; esac
mod="${rel%.lean}"; mod="${mod//\//.}"
run_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)
tc=$(lake env lean --version 2>/dev/null | head -n1 || echo "lean:unknown")
lv=$(lake --version 2>/dev/null | head -n1 || echo "lake:unknown")
src_sha=$(sha256 "$rel")
src_bytes=$(wc -c < "$rel" | tr -d "[:space:]")
last_commit=$(git log -n1 --pretty=format:%H -- "$rel" 2>/dev/null || echo "UNTRACKED")
impt="$TMP/_imports.$$"; : > "$impt"
grep -E "^import[[:space:]]+" "$rel" 2>/dev/null | sed "s/^import[[:space:]]\\+//" | tr -d "\r" | while IFS= read -r line; do for tok in $line; do printf "%s\n" "$tok" >> "$impt"; done; done
hfile="exe/.capsule_each/${mod//./_}.lean"; mkdir -p "$(dirname "$hfile")"; : > "$hfile"
printf "%s\n" "import ${mod}" >> "$hfile"
printf "%s\n" "def _capsule_probe : True := True.intro" >> "$hfile"
start_ms=$(ms_now); build_ok=0; blog="$TMP/_build_${mod//./_}.log"
if lake env lean --make "$hfile" >"$blog" 2>&1; then build_ok=1; fi
end_ms=$(ms_now); dur_ms=0; if [ "$start_ms" != 0 ] && [ "$end_ms" != 0 ]; then dur_ms=$(( end_ms - start_ms )); fi
olean_rel="${rel%.lean}.olean"; olean_path=".lake/build/lib/${olean_rel#src/}"
olean_sha="NONE"; olean_bytes=0; if [ -f "$olean_path" ]; then olean_sha=$(sha256 "$olean_path"); olean_bytes=$(wc -c < "$olean_path" | tr -d "[:space:]"); fi
imps=$(json_arr_from_lines "$impt")
out="$BASE/${mod//./_}.json"; : > "$out"
printf "{" >> "$out"
printf "\"module\":\"%s\"," "$mod" >> "$out"
printf "\"path\":\"%s\"," "$rel" >> "$out"
printf "\"imports\":%s," "$imps" >> "$out"
printf "\"src_sha256\":\"%s\"," "$src_sha" >> "$out"
printf "\"src_bytes\":%s," "$src_bytes" >> "$out"
printf "\"olean_sha256\":\"%s\"," "$olean_sha" >> "$out"
printf "\"olean_bytes\":%s," "$olean_bytes" >> "$out"
printf "\"build_ok\":%s," "$build_ok" >> "$out"
printf "\"build_time_ms\":%s," "$dur_ms" >> "$out"
printf "\"toolchain\":\"%s\"," "$tc" >> "$out"
printf "\"lake\":\"%s\"," "$lv" >> "$out"
printf "\"last_commit\":\"%s\"," "$last_commit" >> "$out"
printf "\"run_utc\":\"%s\"" "$run_utc" >> "$out"
printf "}\n" >> "$out"
