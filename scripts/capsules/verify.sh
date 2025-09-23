#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
export LC_ALL=C LANG=C
IDX="${1:-corridor/capsules/index.tsv}"
SIG="${2:-.tau_ledger/capsules/index.sha256}"
TMP=".tau_ledger/capsules/.vtmp"; mkdir -p "$TMP"
[ -f "$IDX" ] || { echo "[CAPVERIFY] missing index"; exit 2; }
[ -f "$SIG" ] || { echo "[CAPVERIFY] missing signature"; exit 3; }
head -n 1 "$IDX" | tr -d '\r' > "$TMP/.norm.tsv"
tail -n +2 "$IDX" | tr -d '\r' \
  | awk 'BEGIN{OFS="\t"} {sub(/[ \t]+$/,"",$0); if(NF>0) print $0}' \
  | LC_ALL=C sort -u >> "$TMP/.norm.tsv"
CANON=$(sha256sum "$TMP/.norm.tsv" | awk '{print $1}')
STORED=$(tr -d '\r' < "$SIG" | awk '{print $1}')
if [ "$CANON" = "$STORED" ]; then
  echo "[CAPVERIFY] ok"
  exit 0
else
  echo "[CAPVERIFY] mismatch"
  echo "canon=$CANON"
  echo "store=$STORED"
  diff -u --label canon "$TMP/.norm.tsv" --label index "$IDX" || true
  exit 1
fi
