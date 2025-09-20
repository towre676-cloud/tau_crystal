#!/usr/bin/env bash
set -euo pipefail
DOC="analysis/geom/canonical_truths.txt"
LOCK="analysis/geom/canonical_truths.lock"
REC="analysis/geom/canonical_truths.receipt.tsv"
INTTXT="analysis/geom/canonical_truths.intent.txt"
[ -f "$DOC" ] || { echo "::error::missing $DOC"; exit 1; }
cur=$(sha256sum "$DOC" | awk '{print $1}')
printf "HASH\t%s\nFILE\t%s\n" "$cur" "$DOC" > "$LOCK"
python3 - "$DOC" "$REC" <<PY
import sys, time, hashlib, os
doc, rec = sys.argv[1], sys.argv[2]
os.makedirs(os.path.dirname(rec), exist_ok=True)
h = hashlib.sha256(open(doc,"rb").read()).hexdigest()
ts = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
open(rec,"w",encoding="utf-8").write(f"ID\t{h}\nTS\t{ts}\nFILE\t{doc}\n")
PY
[ -f "scripts/geom/bind_intent.py" ] && python3 scripts/geom/bind_intent.py "CANON_MATH" "$INTTXT" "analysis/geom/canonical_truths.intent.receipt.tsv" || true
echo "Lock and receipts refreshed. Commit with RECANONIZE=TRUE in the message."
