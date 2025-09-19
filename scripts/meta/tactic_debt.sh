#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage: ./scripts/meta/tactic_debt.sh <label> -- <command ...>
lab="$1"; shift || true; [ "$1" = "--" ] && shift || true
[ -n "$lab" ] || { echo "[tactic] need label"; exit 2; }
out="metrics/tactic_debt.tsv"; mkdir -p "$(dirname "$out")"
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
start=$(python - <<PY;import time;print(repr(time.time()));PY)
"$@" >/dev/null 2>&1
rc=$?
end=$(python - <<PY;import time;print(repr(time.time()));PY)
dur=$(awk -v a="$start" -v b="$end" "BEGIN{printf(\"%%.3f\", b-a)}")
hdr="ts\tlabel\tduration_s\trc"; [ -s "$out" ] || printf "%s\n" "$hdr" > "$out"
printf "%s\t%s\t%s\t%s\n" "$ts" "$lab" "$dur" "$rc" >> "$out"
echo "[tactic] $lab took ${dur}s rc=$rc"
