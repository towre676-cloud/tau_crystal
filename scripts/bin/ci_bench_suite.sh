#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
scripts/bin/ci_bench_run.sh cold
scripts/bin/ci_bench_run.sh cold
scripts/bin/ci_bench_run.sh cold
scripts/bin/ci_bench_run.sh warm
scripts/bin/ci_bench_run.sh warm
scripts/bin/ci_bench_run.sh warm
scripts/bin/gen_ci_speed_bench.sh
awk -F"|" "NR>2 && \$0 !~ /^\\|---/ { fac=\$8+0; if (fac>max) { max=fac; line=\$0 } } END { if (max>0) { printf(\\"[max] %.2fx\\n%s\\n\\", max, line) } else { print \\"[max] 0.00x\\n[info] no data rows\\" } }" docs/benchmarks/ci_speed.md
