#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ok=0; fail=0
check_file(){ f="$1"; if [ -s "$f" ]; then echo "[ok] $f"; ok=$((ok+1)); else echo "[err] missing or empty: $f"; fail=$((fail+1)); fi }
check_file "docs/freed/alignment_table.md"
check_file "docs/freed/relative_tft_functor.md"
check_file "docs/freed/anomaly_line_trivialization.md"
check_file "docs/freed/tmf_sigma_orientation.md"
if [ "$fail" -gt 0 ]; then echo "[fail] Freed alignment verification failed"; exit 1; else echo "[pass] Freed alignment docs present"; fi
