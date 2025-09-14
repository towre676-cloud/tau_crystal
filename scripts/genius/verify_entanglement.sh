#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
root=".tau_ledger/genius"; set +e; files=$(ls -1 "$root"/entangle-*.meta 2>/dev/null | LC_ALL=C sort); rc=$?; set -e
[ $rc -eq 0 ] || { echo "[err] no entangled receipts"; exit 2; }
corr=0; cnt=0
while IFS= read -r f; do
  v=$(sed -n "s/^tau: //p" "$f" | head -n1); [ -n "$v" ] && corr=$(echo "$corr + $v" | bc -l) || true; cnt=$((cnt+1))
done <<< "$files"
clim=$(echo "scale=10; $cnt * 0.5" | bc -l)
ok=$(echo "$corr > $clim" | bc -l)
test "$ok" = "1" && echo "[OK] entanglement verified" || { echo "[FAIL] entanglement"; exit 1; }
