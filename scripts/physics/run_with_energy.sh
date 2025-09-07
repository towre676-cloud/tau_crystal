#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022

read_energy() {
  python3 - <<'PY' 2>/dev/null || true
from scripts.physics.energy import rapl_joules_snapshot as snap
e = None
try:
    e = snap()
except Exception:
    e = None
print("nan" if e is None else f"{e:.9f}")
PY
}

# Take pre snapshot (may print "nan" if unsupported)
E0="$(read_energy || echo nan)"

# Run the normal physics pipeline (selection + run + post_meas.json)
bash scripts/physics/run_physics.sh || true

# Take post snapshot
E1="$(read_energy || echo nan)"

# Compute delta if both numeric
python3 - <<PY || true
import json, math, pathlib, sys
post_path = pathlib.Path(".tau_ledger/physics/post_meas.json")
try:
    e0 = float("${E0}"); e1 = float("${E1}")
    EJ = max(0.0, e1 - e0)
except Exception:
    EJ = None

if post_path.exists():
    doc = json.loads(post_path.read_text())
    doc.setdefault("measured", {})["E"] = EJ  # None -> null in JSON
    post_path.write_text(json.dumps(doc, indent=2))
    # Recompute/print receipt with the new E (still warn-only for dE)
    try:
        import subprocess
        subprocess.run(["python3","scripts/physics/check_physics.py"], check=False)
    except Exception:
        pass

print(f"[energy] E={('nan' if EJ is None else f'{EJ:.6f}')} J (warn-only)")
PY
