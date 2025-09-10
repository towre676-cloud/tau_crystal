# CI speed benchmarks (receipt-backed)

Run `scripts/bench/bench_local_matrix.sh 5` locally and dispatch “CI Bench” in Actions. Then run `scripts/bench/bench_publish.sh` to compute medians and render the table below from `.tau_ledger/bench/runs.ndjson` and CI artifacts you merge into that file.

| OS | Runner | N(cold) | median_cold_s | N(warm) | median_warm_s | factor (cold/warm) |
|---|---|---:|---:|---:|---:|---:|
| Linux | github-actions | 0 | NA | 0 | NA | NA |
| Darwin | github-actions | 0 | NA | 0 | NA | NA |
| Linux | local | 0 | NA | 0 | NA | NA |
| Darwin | local | 0 | NA | 0 | NA | NA |
