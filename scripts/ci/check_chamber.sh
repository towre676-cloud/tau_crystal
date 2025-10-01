#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cd "$(dirname "$0")/../.." || exit 1
bash scripts/ci/_sanitize_canons.sh
python3 scripts/receipt/bind_receipt.py analysis/chamber/ch_ok_canon.json
python3 scripts/receipt/bind_receipt.py analysis/chamber/ch_bad_canon.json
python3 -c "import json,sys;
J=lambda p: json.load(open(p,'r',encoding='utf-8'));
ok=J('analysis/chamber/ch_ok_canon.json'); bad=J('analysis/chamber/ch_bad_canon.json');
rho=ok['rho']; perm=ok['perm'];
sorted_ok=sorted(rho); perm_ok=[rho[i] for i in perm];
good=(sorted_ok==sorted(perm_ok)) and (len(set(rho))>1);
bad_deg=(len(set(bad['rho']))==1);
print('[chamber] good/permutation:',good,'; bad degenerate:',bad_deg);
sys.exit(0 if (good and bad_deg) else 1)"
