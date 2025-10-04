# FHT dictionary: τ‑Crystal implements the Freed–Hopkins–Teleman correspondence over computation: boundary‑state space of signed receipts as G, the τ‑clock as loop rotation, and the Quillen‑curvature residue as the basic twist; admissible, replay‑equivariant pipelines realize τ‑twisted, conjugation‑equivariant curved Fredholm complexes on G whose K‑classes classify stable execution behaviors, with fusion matching the Verlinde product.
# STRICT policy block BEGIN
: "${STRICT:=0}"
BR="none"
if [ -n "${GITHUB_REF_NAME-}" ]; then
  BR="$GITHUB_REF_NAME"
else
  if command -v git >/dev/null 2>&1; then
    BR=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo none)
  fi
fi
case "$BR" in
  main|release|release/*) STRICT=1 ;;
  *) : ;;
esac
export STRICT
# STRICT policy block END
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
