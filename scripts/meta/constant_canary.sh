#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# JIT-agnostic timing stability smoke: runs a fixed arithmetic loop many times and checks variance.
n="${1:-50}"; thr="${THRESHOLD_PCT:-15}"
vals=""; i=0
while [ "$i" -lt "$n" ]; do
  t0=$(python - <<PY;import time;print(repr(time.perf_counter_ns()));PY)
  j=0; s=0; while [ "$j" -lt 50000 ]; do s=$(( (s + j) ^ 0x9e3779b97f4a7c15 )); j=$((j+1)); done
  t1=$(python - <<PY;import time;print(repr(time.perf_counter_ns()));PY)
  d=$((t1 - t0)); vals="$vals $d"; i=$((i+1))
done
min=; max=; for v in $vals; do [ -z "$min" ] && min="$v" || { [ "$v" -lt "$min" ] && min="$v"; }; [ -z "$max" ] && max="$v" || { [ "$v" -gt "$max" ] && max="$v"; }; done
pct=$(awk -v lo="$min" -v hi="$max" "BEGIN{if(lo<=0){print 100}else{print (hi-lo)*100.0/lo}}")
echo "[canary] min=$min ns max=$max ns spread_pct=$pct threshold=$thr"
awk -v p="$pct" -v t="$thr" "BEGIN{exit(p>t?1:0)}" || { echo "[canary] variance too high"; exit 1; }
