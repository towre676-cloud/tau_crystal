#!/usr/bin/env bash
# CI bench: cold vs lake_cache vs zip_roundtrip vs onefile
set -euo pipefail
set +H

LEDGER=".tau_ledger"; OUT="$LEDGER/ci_bench_$(date -u +%Y%m%dT%H%M%SZ).json"
mkdir -p "$LEDGER"

# choose /usr/bin/time -v if present for memory; else plain bash timing
TIMEBIN=""
if [ -x /usr/bin/time ]; then TIMEBIN="/usr/bin/time -v"; fi

ts(){ date -u +%Y-%m-%dT%H:%M:%SZ; }
sha_file(){ test -f "$1" && sha256sum "$1" 2>/dev/null | awk "{print \$1}" || echo ""; }
sha_bin(){ command -v "$1" >/dev/null 2>&1 && sha256sum "$(command -v "$1")" | awk "{print \$1}" || echo ""; }

# fingerprint (kernel, glibc, image label if present)
fp_kernel(){ uname -srmo 2>/dev/null || uname -a; }
fp_glibc(){ (ldd --version 2>/dev/null || true) | head -n1 | tr -s " "; }
fp_image(){ printf "%s/%s" "${ImageVersion:-}" "${ImageOS:-}" | sed "s#^/##" ; }

# tidy clean between runs
wipe(){ rm -rf .lake build lake-packages 2>/dev/null || true; mkdir -p .lake; }

run_cmd(){
  local label="$1"; shift
  local log="$(mktemp)"; local mlog="$(mktemp)"; local start end wall mem
  start=$(date +%s)
  if [ -n "$TIMEBIN" ]; then
