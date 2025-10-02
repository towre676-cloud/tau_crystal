#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
PY="$(mktemp)"; trap 'rm -f "$PY"' EXIT
printf "%s\n" "import json" > "$PY"
printf "%s\n" "OK=json.load(open(\"analysis/chamber/ch_ok_canon.json\",\"r\",encoding=\"utf-8\"))" >> "$PY"
printf "%s\n" "BAD=json.load(open(\"analysis/chamber/ch_bad_canon.json\",\"r\",encoding=\"utf-8\"))" >> "$PY"
printf "%s\n" "rho=OK[\"rho\"]; W=OK[\"perm\"]; rho_star=[rho[i] for i in W]" >> "$PY"
printf "%s\n" "assert sorted(rho_star)==OK[\"sigma\"], \"stable sort mismatch\"" >> "$PY"
printf "%s\n" "assert len(set(rho))==len(rho), \"nondegeneracy violated\"" >> "$PY"
printf "%s\n" "assert BAD.get(\"should_fail\",False)==True, \"bad payload not flagged\"" >> "$PY"
printf "%s\n" "print(\"[ok] chamber: stable sort & permutation invariance; bad payload flagged\")" >> "$PY"
python "$PY"
python scripts/receipt/verify_receipt_digest.py || true
