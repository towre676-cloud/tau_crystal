#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cd "$(dirname "$0")/../.." || exit 1
echo "[ci] anomaly glue check — start"
for p in analysis/anomaly/anomaly_M1_canon.json analysis/anomaly/anomaly_M2_canon.json analysis/anomaly/anomaly_glued_canon.json analysis/anomaly/anomaly_glued_bad_canon.json; do [ -s "$p" ] || { echo "[ci] missing $p" >&2; exit 2; }; done
mkdir -p .tau_ledger
for p in analysis/anomaly/anomaly_M1_canon.json analysis/anomaly/anomaly_M2_canon.json analysis/anomaly/anomaly_glued_canon.json analysis/anomaly/anomaly_glued_bad_canon.json; do
  echo "[ci] bind $p"
  python3 scripts/receipt/bind_receipt.py "$p"
done
python3 -c "import json,sys; J=lambda p: json.load(open(p, 'r', encoding='utf-8')); m1=J('analysis/anomaly/anomaly_M1_canon.json'); m2=J('analysis/anomaly/anomaly_M2_canon.json'); g=J('analysis/anomaly/anomaly_glued_canon.json'); b=J('analysis/anomaly/anomaly_glued_bad_canon.json'); T=m1['torsion']; assert T==m2['torsion']==g['torsion']==b['torsion'], 'torsion mismatch'; left=(m1['h']*m2['h'])%T; gm=g['h']%T; bm=b['h']%T; print([glue-ok], left, gm, left==gm); print([glue-bad], left, bm, left!=bm); sys.exit(0 if (left==gm and left!=bm) else 1)"
R1=$(ls -1t .tau_ledger/anomaly_M1_canon_*.receipt.json      | head -n1)
R2=$(ls -1t .tau_ledger/anomaly_M2_canon_*.receipt.json      | head -n1)
R3=$(ls -1t .tau_ledger/anomaly_glued_canon_*.receipt.json   | head -n1)
R4=$(ls -1t .tau_ledger/anomaly_glued_bad_canon_*.receipt.json | head -n1)
[ -n "${R1:-}" ] && [ -n "${R2:-}" ] && [ -n "${R3:-}" ] && [ -n "${R4:-}" ] || { echo "[ci] missing receipts" >&2; exit 3; }
python3 scripts/receipt/verify_receipt_digest.py "$R1" "$R2" "$R3" "$R4"
echo "[ci] anomaly glue check — OK"
