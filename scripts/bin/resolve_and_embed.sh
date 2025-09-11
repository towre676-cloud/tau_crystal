#!/usr/bin/env bash
set -euo pipefail; set +H
REC="${1:?path to receipt.json}"
H_IN="$(jq -r ".input_sha256" "$REC" 2>/dev/null || grep -o "\"input_sha256\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$REC" | sed -E "s/.*:\"([^\"]*)\".*/\\1/")"
[ -n "$H_IN" ] || { echo "[err] no input_sha256 in $REC"; exit 2; }
CAND="$(scripts/bin/scan_hash_match.sh "$H_IN" 2>/dev/null || true)"
if [ -n "$CAND" ]; then
  [ -x scripts/bin/receipt_set_contract.py ] || {
    F="scripts/bin/receipt_set_contract.py"; : > "$F"
    printf "%s\n" "#!/usr/bin/env python3"                                >> \"$F\"
    printf "%s\n" "import sys, json, pathlib"                             >> \"$F\"
    printf "%s\n" "rec=pathlib.Path(sys.argv[1]); c=sys.argv[2]"          >> \"$F\"
    printf "%s\n" "o=json.loads(rec.read_text(encoding=\"utf-8\"))"       >> \"$F\"
    printf "%s\n" "o[\"contract_path\"]=c"                                 >> \"$F\"
    printf "%s\n" "rec.write_text(json.dumps(o,ensure_ascii=False,separators=(\",\",\":\"),sort_keys=True),encoding=\"utf-8\")" >> \"$F\"
    chmod +x "$F"
  }
  python3 scripts/bin/receipt_set_contract.py "$REC" "$CAND"
  echo "[ok] embedded contract_path: $CAND"
  scripts/bin/verify_receipt.sh "$REC" "$CAND"
else
  echo "[warn] no file in repo matches input_sha256 for $REC"
  echo "[hint] try verifying against request.input or export the engine's effective input JSON"
fi
