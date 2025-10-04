#!/usr/bin/env bash
# minimal CI harness (MSYS-safe, no set -e; idempotent calls guarded)
umask 022; export LC_ALL=C LANG=C
: "${STRICT:=0}"

# run available diagnostics (advisory)
[ -x scripts/ci/emit_curvature_samples.sh ] && scripts/ci/emit_curvature_samples.sh || :
[ -x scripts/ci/emit_curvature_rich.sh ]   && scripts/ci/emit_curvature_rich.sh   || :
[ -x scripts/ci/hecke_guard.sh ]           && scripts/ci/hecke_guard.sh           || :
[ -x scripts/ci/fft_scan.sh ]              && scripts/ci/fft_scan.sh              || :
[ -x scripts/ci/anomaly_budget.sh ]        && scripts/ci/anomaly_budget.sh        || :
[ -x scripts/ci/anomaly_report.sh ]        && scripts/ci/anomaly_report.sh        || :
