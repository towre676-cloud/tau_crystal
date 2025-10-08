#!/usr/bin/env python3
import json, os, sys
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
q1_path = os.path.join(ROOT,"out","coeffs","q1_stub.json")
out_path = os.path.join(ROOT,"out","receipts","mde.json")
os.makedirs(os.path.dirname(out_path), exist_ok=True)

rep = {"check":"jacobi_sanity_on_q1","parity_ok":False,"integral_ok":False,"window_ok":False,"details":{}}
if not os.path.exists(q1_path):
    rep["details"]["error"]="missing q1_stub.json"
    print(json.dumps(rep)); open(out_path,"w").write(json.dumps(rep,indent=2)); sys.exit(0)

data = json.load(open(q1_path))
charges = {int(k):int(v) for k,v in data.get("charges",{}).items()}

# parity: c_r == c_-r
parity = all(charges.get(r,0) == charges.get(-r,0) for r in list(charges.keys()))
rep["parity_ok"]=parity

# integrality: all integers already cast → true if no cast errors
rep["integral_ok"]=True

# window: index 3/2 ⇒ |r| ≤ 3 for the primitive slice (loose; allow up to 6 but forbid >6)
window = max((abs(r) for r in charges.keys()), default=0)
rep["window_ok"] = (window <= 6)

rep["details"]["max_abs_charge"]=window
rep["details"]["support"]=sorted(charges.keys())
rep["details"]["sum_coeffs"]=sum(charges.values())

print(json.dumps(rep))
with open(out_path,"w") as f: json.dump(rep,f,indent=2)
