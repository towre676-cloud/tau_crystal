#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$CD" || exit 1
REC="receipts/k3_next_receipt.json"; LOC="data/k3_next_local_signs.csv"; OUT="receipts/k3_next_root_number.json"
[ -s "$REC" ] && [ -s "$LOC" ] || { echo "missing $REC or $LOC" >&2; exit 2; }
python scripts/safe/root_number.py "$REC" "$LOC" "$OUT"
arch=$(python scripts/safe/json_read.py archimedean "$OUT")
glob=$(python scripts/safe/json_read.py global "$OUT")
[ -n "$arch" ] && [ "$arch" != "None" ] && [ -n "$glob" ] && [ "$glob" != "None" ] || { echo "insufficient data to set global root number" >&2; exit 3; }
python - "$REC" "$glob" <<PY
import io,sys,json
p,g=sys.argv[1],sys.argv[2]
with io.open(p,"r",encoding="utf-8") as f: R=json.load(f)
R.setdefault("curve",{}).update({"root_number": g})
with io.open(p,"w",encoding="utf-8") as f: f.write(json.dumps(R,separators=(",",":"))+"\n")
PY
printf "%s\n" "root_number set to $glob"
