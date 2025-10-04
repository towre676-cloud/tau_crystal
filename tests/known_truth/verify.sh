#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ROOT="$(cd "$(dirname "$0")/../.." && pwd -P)"
LEDGER_DIR="${LEDGER_DIR:-.tau_ledger}"
mkdir -p "$LEDGER_DIR"
out="$LEDGER_DIR/KNOWN_TRUTH_RESULTS.tsv"
: > "$out"; printf "test\tstatus\tvalue\tthreshold\n" >> "$out"
fail=0
pfile="$ROOT/tests/known_truth/motives/period_demo.tsv"
dfile="$ROOT/tests/known_truth/motives/period_declared.txt"
psum=$(awk "NR>1 {s+=\$2} END{printf \"%.12f\", (s+0)}" "$pfile")
pdec=$(awk "NR==1 {printf \"%.12f\", \$1+0}" "$dfile")
diff=$(awk -v a="$psum" -v b="$pdec" "BEGIN{printf \"%.12f\", (a-b)}")
abs=$(awk -v x="$diff" "BEGIN{ if (x<0) x=-x; printf \"%.12f\", x }")
tol="0.000000500000"
if awk -v a="$abs" -v t="$tol" "BEGIN{exit !(a<=t)}"; then
  printf "period_demo\tPASS\t%s\t%s\n" "$abs" "$tol" >> "$out"
else
  printf "period_demo\tFAIL\t%s\t%s\n" "$abs" "$tol" >> "$out"; fail=1
fi
cfile="$ROOT/tests/known_truth/curvature/null_curvature.tsv"
csum=$(awk "{s+=\$2} END{printf \"%.12f\", (s+0)}" "$cfile")
cabs=$(awk -v x="$csum" "BEGIN{ if (x<0) x=-x; printf \"%.12f\", x }")
ctol="0.000000050000"
if awk -v a="$cabs" -v t="$ctol" "BEGIN{exit !(a<=t)}"; then
  printf "curvature_null\tPASS\t%s\t%s\n" "$cabs" "$ctol" >> "$out"
else
  printf "curvature_null\tFAIL\t%s\t%s\n" "$cabs" "$ctol" >> "$out"; fail=1
fi
ka="$ROOT/tests/known_truth/kclass/runA.boundary"
kb="$ROOT/tests/known_truth/kclass/runB.boundary"
if cmp -s "$ka" "$kb"; then
  printf "kclass_proxy\tPASS\t0\t0\n" >> "$out"
else
  # Fallback: compare SHA256 if available to tolerate trivial line ending drift.
  h1=$( (command -v sha256sum >/dev/null 2>&1 && sha256sum "$ka" | awk "{print \$1}") || (command -v shasum >/dev/null 2>&1 && shasum -a 256 "$ka" | awk "{print \$1}") || echo "")
  h2=$( (command -v sha256sum >/dev/null 2>&1 && sha256sum "$kb" | awk "{print \$1}") || (command -v shasum >/dev/null 2>&1 && shasum -a 256 "$kb" | awk "{print \$1}") || echo "x")
  if [ -n "$h1" ] && [ "$h1" = "$h2" ]; then
    printf "kclass_proxy\tPASS\t0\t0\n" >> "$out"
  else
    printf "kclass_proxy\tFAIL\t1\t0\n" >> "$out"; fail=1
  fi
fi
echo "[known-truth] results → $out"; cat "$out" | sed 1q >/dev/null || true
exit "$fail"
