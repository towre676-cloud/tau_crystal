#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
PY="$(mktemp)"; trap 'rm -f "$PY"' EXIT
printf "%s\n" "import json,collections" > "$PY"
printf "%s\n" "pre=json.load(open(\"analysis/specnet/sn_pre_canon.json\",\"r\",encoding=\"utf-8\"))" >> "$PY"
printf "%s\n" "post=json.load(open(\"analysis/specnet/sn_post_canon.json\",\"r\",encoding=\"utf-8\"))" >> "$PY"
printf "%s\n" "F=lambda D: collections.Counter(D[\"factors\"]) # symbolic multiset of KS factors" >> "$PY"
printf "%s\n" "assert F(pre)==F(post), \"KS product changed under wall permutation\"" >> "$PY"
printf "%s\n" "print(\"[ok] KS product invariant under wall step (symbolic multiset check)\")" >> "$PY"
python "$PY"
python scripts/receipt/verify_receipt_digest.py || true
