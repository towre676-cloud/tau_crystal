# Use work-stealing for dynamic load balancing
jobs=(); for shard in $(seq 1 "$total"); do jobs+=("$shard"); done
for job in "${jobs[@]}"; do
  if [ "$(jobs -r | wc -l)" -lt "$n" ]; then
    "$cmd" "$job" >"$tmpdir/$job.out" 2>"$tmpdir/$job.err" &
  else
    wait -n || { cat "$tmpdir"/*.err; exit 1; }
  fi
done
