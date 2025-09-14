#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
rec="${1:-}"; [ -s "$rec" ] || { echo "usage: $0 <receipt.json>"; exit 2; }
root=".tau_ledger/tau_bin"; mkdir -p "$root"; ts=$(date -u +%Y%m%dT%H%M%SZ); f="$root/binv1-$ts.meta"
need1=$(grep -q "\"commit\"" "$rec" && echo 1 || echo 0)
need2=$(grep -q "\"merkle_root\"" "$rec" && echo 1 || echo 0)
need3=$(grep -q "\"wrapper_digest\"" "$rec" && echo 1 || echo 0)
[ "$need1$need2$need3" = "111" ] || { echo "[FAIL] invalid receipt schema"; exit 1; }
sha=$(sha256sum "$rec" | awk '{print $1}')
: > "$f"
printf '%s\n' "schema: taucrystal/bin/v1" >> "$f"
printf '%s\n' "id: binv1-$ts" >> "$f"
printf '%s\n' "utc: $ts" >> "$f"
printf '%s\n' "receipt: $(basename "$rec")" >> "$f"
printf '%s\n' "sha256: $sha" >> "$f"
printf '%s\n' "status: PASS" >> "$f"
echo "[OK] verified receipt: $rec"
