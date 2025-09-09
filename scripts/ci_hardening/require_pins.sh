#!/usr/bin/env bash
set -euo pipefail
set +H
fail=0
for y in .github/workflows/*.yml .github/workflows/*.yaml; do
  [ -f "$y" ] || continue
  sed -i 's/\r$//' "$y" 2>/dev/null || true
  if grep -Eq 'runs-on:[[:space:]]*ubuntu-latest' "$y"; then echo "[err] $y uses ubuntu-latest; pin e.g. ubuntu-22.04" >&2; fail=1; fi
  if grep -Eq 'uses:[[:space:]]*[^@]+@[[:alnum:].-]*v[0-9]' "$y"; then echo "[err] $y uses tag versions; pin to full commit SHA" >&2; fail=1; fi
done
exit $fail
