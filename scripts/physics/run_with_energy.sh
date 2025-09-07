#!/usr/bin/env bash
set -euo pipefail

snap() {
  python3 - <<'PY'
from scripts.physics.energy import rapl_joules_snapshot as s
x = s()
print(x if x is not None else -1.0)
PY
}

pre=$(snap || echo -1)
# Run the normal physics job; it will write post_meas.json with T and E=nan
bash scripts/physics/run_physics.sh || true
post=$(snap || echo -1)

# If RAPL is available, write E; otherwise leave as-is
python3 - <<PY
import json, os, math
p=".tau_ledger/physics/post_meas.json"
try:
    doc=json.load(open(p, "r", encoding="utf-8"))
except Exception:
    doc={"measured":{}}
doc.setdefault("measured",{})
pre=float(os.environ.get("PRE","-1"))
post=float(os.environ.get("POST","-1"))
E = post - pre if (pre>0 and post>0) else float("nan")
if E is not None and not math.isnan(E) and E>=0.0:
    doc["measured"]["E"]=E
    print(f"[energy] E={E:.6f} J (warn-only)")
else:
    print("[energy] RAPL not available; leaving E as nan (warn-only)")
open(p,"w",encoding="utf-8").write(json.dumps(doc,indent=2))
PY
