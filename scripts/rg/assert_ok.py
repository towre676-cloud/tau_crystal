#!/usr/bin/env python3
import json, sys
from pathlib import Path
p=Path(".tau_ledger/rg/affine_leaf.json")
if not p.exists():
  print("[rg] missing receipt"); sys.exit(2)
d=json.loads(p.read_text(encoding="utf-8"))
ol=d["one_loop"]; tol=1e-12; errs=[]
for k in ("invariant_residual","fisher_relation_residual","amplitude_vs_dF_residual"):
  v=float(ol[k])
  if abs(v)>tol: errs.append(f"{k}={v}")
print("[rg] mu={} inv={} fisher_res={} dF_res={}".format(ol["mu"],ol["invariant_residual"],ol["fisher_relation_residual"],ol["amplitude_vs_dF_residual"]))
if errs:
  print("[rg] residuals exceed tol:", ", ".join(errs)); sys.exit(2)
sys.exit(0)
