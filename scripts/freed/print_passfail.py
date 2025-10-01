#!/usr/bin/env python3
import json,glob
xs=sorted(glob.glob("analysis/freed/axioms_passfail_*.json"))
print("[warn] no analysis/freed/axioms_passfail_*.json found") if not xs else None
if xs:
  p=xs[-1]; print("PASS/FAIL ->",p); d=json.load(open(p,"r",encoding="utf-8"))
  for k,v in d.get("passfail",{}).items(): print(f"{k:24s}: {v}")
