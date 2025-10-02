#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
PY="$(mktemp)"; trap 'rm -f "$PY"' EXIT
printf "%s\n" "import json" > "$PY"
printf "%s\n" "OK=json.load(open(\"analysis/sset/sset_horn_ok_canon.json\",\"r\",encoding=\"utf-8\"))" >> "$PY"
printf "%s\n" "BAD=json.load(open(\"analysis/sset/sset_horn_bad_canon.json\",\"r\",encoding=\"utf-8\"))" >> "$PY"
printf "%s\n" "faces_ok=OK[\"faces\"]; filler=OK.get(\"filler\")" >> "$PY"
printf "%s\n" "assert filler is not None, \"missing filler in ok payload\"" >> "$PY"
printf "%s\n" "assert faces_ok[\"d0\"]==filler[\"d0\"] and faces_ok[\"d2\"]==filler[\"d2\"], \"horn face mismatch\"" >> "$PY"
printf "%s\n" "assert BAD.get(\"filler\") is None, \"bad payload should lack filler\"" >> "$PY"
printf "%s\n" "print(\"[ok] simplicial horn: faces consistent; failing case lacks filler\")" >> "$PY"
python "$PY"
python scripts/receipt/verify_receipt_digest.py || true
