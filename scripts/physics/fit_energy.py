#!/usr/bin/env python3
import json, sys

def jload(p):
    try:
        with open(p, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return None

pre   = jload(".tau_ledger/physics/pre_cert.json")
post  = jload(".tau_ledger/physics/post_meas.json")
pfile = ".tau_ledger/physics/passport.json"
passp = jload(pfile) or {}

if not pre or not post:
    print("[energy-fit] missing pre/post json; skip")
    sys.exit(0)

try:
    n = pre["selected"]["n"]
    k = pre["selected"]["k"]
    w1 = pre["models"]["W"]["w1"]
    w2 = pre["models"]["W"]["w2"]
    W = (w1 + w2*k) * n
    E = post.get("measured", {}).get("E", None)

    if E is None or not isinstance(E, (int, float)) or E <= 0:
        print("[energy-fit] no measured E>0; skip")
        sys.exit(0)
    if W <= 0:
        print("[energy-fit] nonpositive W; skip")
        sys.exit(0)

    c_energy = E / W
    passp.setdefault("coefficients", {})["c_energy"] = float(c_energy)
    with open(pfile, "w", encoding="utf-8") as f:
        json.dump(passp, f, indent=2)
    print(f"[energy-fit] stamped coefficients.c_energy = {c_energy:.6e} J/item")
except Exception as e:
    print("[energy-fit] error:", e)
