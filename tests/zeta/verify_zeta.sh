#!/usr/bin/env bash
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
LEDGER_DIR=${LEDGER_DIR:-.tau_ledger}
mkdir -p "$LEDGER_DIR"

eigs="tests/zeta/A_2x2.eigs.tsv"
detf="tests/zeta/A_2x2.det.txt"
out="$LEDGER_DIR/KNOWN_TRUTH_RESULTS.tsv"

# -ζ'(0) = Σ ln λ
sumln=$(awk 'NR>1{acc+=log($1)} END{printf "%.12f",(acc+0)}' "$eigs")
neg_zeta_prime="$sumln"

# ln det(A) from exact det
ln_det=$(awk '{printf "%.12f", log($1)}' "$detf")

diff=$(awk -v a="$neg_zeta_prime" -v b="$ln_det" 'BEGIN{printf "%.12f", (a-b)}')
abs=$(awk -v x="$diff" 'BEGIN{if(x<0)x=-x; printf "%.12f", x }')
tol="0.000000001000"

# Write/append machine-readable result
if [ ! -f "$out" ]; then printf "test\tstatus\tvalue\tthreshold\n" > "$out"; fi
if awk -v a="$abs" -v t="$tol" 'BEGIN{exit !(a<=t)}'; then
  printf "zeta_residue_2x2\tPASS\t%s\t%s\n" "$abs" "$tol" >> "$out"
else
  printf "zeta_residue_2x2\tFAIL\t%s\t%s\n" "$abs" "$tol" >> "$out"
fi

# Emit a curvature TSV from mean-centered log-eigs (sum ~ 0)
ts=$(date -u +%Y%m%dT%H%M%SZ 2>/dev/null || env TZ=UTC date +%Y%m%dT%H%M%SZ || date +%Y%m%dT%H%M%SZ)
curv="$LEDGER_DIR/${ts}_curvature.tsv"
l1=$(awk 'NR==2{printf "%.12f", log($1)}' "$eigs")
l2=$(awk 'NR==3{printf "%.12f", log($1)}' "$eigs")
mean=$(awk -v a="$l1" -v b="$l2" 'BEGIN{printf "%.12f", (a+b)/2}')
d1=$(awk -v x="$l1" -v m="$mean" 'BEGIN{printf "%.12f", x-m}')
d2=$(awk -v x="$l2" -v m="$mean" 'BEGIN{printf "%.12f", x-m}')
: > "$curv"
printf "eig1\t%s\n" "$d1" >> "$curv"
printf "eig2\t%s\n" "$d2" >> "$curv"
echo "[zeta] -zeta'(0)=$neg_zeta_prime  ln(det A)=$ln_det  |Δ|=$abs  -> $curv"
