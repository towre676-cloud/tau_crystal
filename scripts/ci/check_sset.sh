#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cd "$(dirname "$0")/../.." || exit 1
bash scripts/ci/_sanitize_canons.sh
python3 scripts/receipt/bind_receipt.py analysis/sset/sset_ok_canon.json
python3 scripts/receipt/bind_receipt.py analysis/sset/sset_bad_canon.json
python3 - <<'PY'
import json, sys
J=lambda p: json.load(open(p,'r',encoding='utf-8'))
ok=J('analysis/sset/sset_ok_canon.json'); bad=J('analysis/sset/sset_bad_canon.json')
faces_ok=set(map(tuple, ok['faces'].values()))
faces_bad=set(map(tuple, bad['faces'].values()))
has_filler = ('filler' in ok) and isinstance(ok['filler'], list)
cond = (len(faces_ok)==3) and has_filler and (faces_ok==faces_bad)
print("[sset] horn ok:", cond)
sys.exit(0 if cond else 1)
PY
