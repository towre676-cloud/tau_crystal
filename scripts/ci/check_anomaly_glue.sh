#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cd "$(dirname "$0")/../.." || exit 1
bash scripts/ci/_sanitize_canons.sh
echo "[ci] anomaly glue check — start"
mkdir -p .tau_ledger
for p in analysis/anomaly/anomaly_M1_canon.json analysis/anomaly/anomaly_M2_canon.json analysis/anomaly/anomaly_glued_canon.json analysis/anomaly/anomaly_glued_bad_canon.json; do
  echo "[ci] bind $p"; python3 scripts/receipt/bind_receipt.py "$p"
done
python3 -c "import json,sys; J=lambda p: json.load(open(p, 'r', encoding='utf-8')); m1=J('analysis/anomaly/anomaly_M1_canon.json'); m2=J('analysis/anomaly/anomaly_M2_canon.json'); g=J('analysis/anomaly/anomaly_glued_canon.json'); b=J('analysis/anomaly/anomaly_glued_bad_canon.json'); T=m1['torsion']; assert T==m2['torsion']==g['torsion']==b['torsion'], 'torsion mismatch'; left=(m1['h']*m2['h'])%T; gm=g['h']%T; bm=b['h']%T; print('[glue-ok]', left, gm, left==gm); print('[glue-bad]', left, bm, left!=bm); sys.exit(0 if (left==gm and left!=bm) else 1)"
