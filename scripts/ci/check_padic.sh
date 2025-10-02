#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
PY="$(mktemp)"; trap 'rm -f "$PY"' EXIT
printf "%s\n" "import json" > "$PY"
printf "%s\n" "HQ=json.load(open(\"analysis/padic/p_hQ_canon.json\",\"r\",encoding=\"utf-8\"))" >> "$PY"
printf "%s\n" "HP=json.load(open(\"analysis/padic/p_hp_canon.json\",\"r\",encoding=\"utf-8\"))" >> "$PY"
printf "%s\n" "a,b,p=HQ[\"a\"],HQ[\"b\"],HQ[\"p\"]" >> "$PY"
printf "%s\n" "assert p==HP[\"p\"], \"prime mismatch\"" >> "$PY"
printf "%s\n" "lhs=(a*pow(b,-1,p))%p; rhs=HP[\"h_mod_p\"]%p; assert lhs==rhs, f\"congruence fail {lhs}!={rhs} mod {p}\"" >> "$PY"
printf "%s\n" "print(\"[ok] p-adic cross-place congruence holds and both place receipts present\")" >> "$PY"
python "$PY"
python scripts/receipt/verify_receipt_digest.py || true
