#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cd "$(dirname "$0")/../.." || exit 1
bash scripts/ci/_sanitize_canons.sh
python3 scripts/receipt/bind_receipt.py analysis/padic/p_canon.json
python3 - <<'PY'
import json, sys
d=json.load(open('analysis/padic/p_canon.json','r',encoding='utf-8'))
a=d['h']['num'] % d['p']
b=d['h']['den'] % d['p']
p=d['p']
inv=None
for x in range(1,p):
    if (b*x) % p == 1:
        inv = x
        break
res = (a * (inv if inv is not None else 0)) % p
print("[padic] (a/b) mod p =", res, "; inverse exists:", inv is not None)
sys.exit(0 if inv is not None else 1)
PY
