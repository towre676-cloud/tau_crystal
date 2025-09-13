#!/usr/bin/env bash
# lines: 63
# Aggregate quick repo sanity + ledger checks; emit report + exit status (0/1).
set -Eeuo pipefail; set +H; umask 022
ts="$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ)"
outdir=".tau_ledger/gates"; mkdir -p "$outdir"
rep="$outdir/pgv1-$ts.txt"
ok=0; fail=0

note(){ printf '%s\n' "$1" | tee -a "$rep"; }
pass(){ ok=$((ok+1)); note "[OK]  $1"; }
failf(){ fail=$((fail+1)); note "[FAIL] $1"; }

# checks
[ -s ".tau_ledger/CHAIN" ] && pass "CHAIN present" || failf "CHAIN missing/empty"
[ -s "docs/manifest.md" ]  && pass "manifest present" || failf "manifest missing/empty"

# latest timefold verifies?
if latest_meta="$(ls -1 .tau_ledger/timefolds/tf-*.meta 2>/dev/null | LC_ALL=C sort | tail -1)"; then
  if scripts/timefold/verify_timefold.sh "$latest_meta" >/dev/null 2>&1; then
    pass "latest timefold verifies"
  else
    failf "latest timefold fails verification"
  fi
else
  note "[info] no timefolds found"
fi

# qr witness exists (if any witness exists)
if [ -d ".tau_ledger/entropy" ] || [ -d ".tau_ledger/sheaf" ]; then
  [ -s ".tau_ledger/qr/qr-witness.svg" ] && pass "qr witness exists" || failf "qr witness missing"
else
  note "[info] no witnesses yet to QR"
fi

note ""
note "summary: ok=$ok fail=$fail @ $ts"
[ $fail -eq 0 ] && { note "[OK] policy gate v1 passed"; exit 0; } || { note "[FAIL] policy gate v1 failed"; exit 1; }
