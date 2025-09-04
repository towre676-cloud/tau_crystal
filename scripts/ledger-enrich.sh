#!/usr/bin/env bash
set -euo pipefail
IN="${1:?input manifest}"; OUT="${2:-enriched.json}"
if command -v jq >/dev/null 2>&1; then
  jq '. + {"enriched_at": now | todate, "enriched_by":"tau_crystal"}' "$IN" > "$OUT"
else
  python - <<'PY' "$IN" "$OUT"
import json,sys,datetime
j=json.load(open(sys.argv[1]))
j["enriched_at"]=datetime.datetime.utcnow().isoformat()+"Z"
j["enriched_by"]="tau_crystal"
json.dump(j,open(sys.argv[2],"w"),separators=(",",":"))
PY
fi
echo "wrote $OUT"
