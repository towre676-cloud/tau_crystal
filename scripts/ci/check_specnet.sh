#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cd "$(dirname "$0")/../.." || exit 1
bash scripts/ci/_sanitize_canons.sh
python3 scripts/receipt/bind_receipt.py analysis/specnet/sn_pre_canon.json
python3 scripts/receipt/bind_receipt.py analysis/specnet/sn_post_canon.json
python3 -c "import json,sys; J=lambda p: json.load(open(p,'r',encoding='utf-8')); pre=J('analysis/specnet/sn_pre_canon.json'); post=J('analysis/specnet/sn_post_canon.json');
ks=lambda ch,Om: {g:sum(Om[x] for x in ch if x==g) for g in ch}; ok=(ks(pre['charges'],pre['Omega'])==ks(post['charges'],post['Omega']));
print('[specnet] KS preserved:', ok); sys.exit(0 if ok else 1)"
