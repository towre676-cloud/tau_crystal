#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
ts=$(date -u +%Y%m%dT%H%M%SZ)
out_dir=".tau_ledger/gates"; mkdir -p "$out_dir"
report="$out_dir/report.$ts.txt"; latest="$out_dir/report.latest.txt"; latest_ptr="$out_dir/latest.txt"; latest_sha="$out_dir/report.latest.sha256"
commit=$(git rev-parse HEAD 2>/dev/null || echo na)
branch=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo na)
env_sha=$(env | LC_ALL=C sort | tr -d "\r" | sha256sum | awk "{print \$1}")
dotv=$(dot -V 2>&1 || echo "dot N/A")
jqv=$(jq --version 2>/dev/null || echo "jq N/A")
: > "$report"
printf "cathedral-gates report %s\n" "$ts" >> "$report"
printf "commit %s\nbranch %s\nenv_sha %s\n" "$commit" "$branch" "$env_sha" >> "$report"
printf "tools %s | %s\n" "$dotv" "$jqv" >> "$report"
printf "----\n" >> "$report"
run_gate(){ name="$1"; shift; printf "gate %s: " "$name" >> "$report"; if bash "$@" >> "$report" 2>&1; then printf "PASS\n" >> "$report"; return 0; else rc=$?; printf "FAIL (rc=%s)\n" "$rc" >> "$report"; return "$rc"; fi; }
all_ok=0
run_gate "invariants" scripts/gates/invariants.sh || all_ok=1
run_gate "forensics" scripts/gates/forensics_guard.sh || all_ok=1
run_gate "tanh_lineage" scripts/dynamics/tanh_lineage_lock.sh || all_ok=1
printf "----\n" >> "$report"
if [ "$all_ok" -eq 0 ]; then printf "SUMMARY PASS\n" >> "$report"; else printf "SUMMARY FAIL\n" >> "$report"; fi
cp -f "$report" "$latest"
printf "%s\n" "$report" > "$latest_ptr"
sha256sum "$latest" | awk "{print \$1}" > "$latest_sha"
printf "[GATES] wrote %s\n" "$report"
exit "$all_ok"
