#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum | cut -d" " -f1; else shasum -a256 | cut -d" " -f1; fi; }
root="$PWD"; d1=$(mktemp -d); d2=$(mktemp -d); trap 'rm -rf "$d1" "$d2"' EXIT
git -c core.autocrlf=false clone --no-local --quiet . "$d1" >/dev/null
git -c core.autocrlf=false clone --no-local --quiet . "$d2" >/dev/null
( cd "$d1" && bash scripts/ops/assure_strict.sh >/dev/null && bash scripts/ops/verify_offline.sh >/dev/null )
( cd "$d2" && bash scripts/ops/assure_strict.sh >/dev/null && bash scripts/ops/verify_offline.sh >/dev/null )
l1=$(tail -n1 "$d1/.tau_ledger/CHAIN")
l2=$(tail -n1 "$d2/.tau_ledger/CHAIN")
[ "$l1" = "$l2" ] || { echo "[repro] CHAIN leaf diverged"; exit 3; }
r1=$(awk "{print \$2}" <<<"$l1") ; r2=$(awk "{print \$2}" <<<"$l2")
t1=$(sha < "$d1/$r1") ; t2=$(sha < "$d2/$r2")
[ "$t1" = "$t2" ] || { echo "[repro] receipt content diverged"; exit 3; }
if [ -s "$d1/analysis/laurent_ring.tsv" ] && [ -s "$d2/analysis/laurent_ring.tsv" ]; then
  a1=$(tail -n1 "$d1/analysis/laurent_ring.tsv"); a2=$(tail -n1 "$d2/analysis/laurent_ring.tsv"); [ "$a1" = "$a2" ] || { echo "[repro] laurent row diverged"; exit 3; }
fi
echo "[repro] two-clone equivalence holds"
