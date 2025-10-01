#!/usr/bin/env python3
import json,glob,os,datetime; from pathlib import Path
def newest(pats):
  C=[]
  for pat in pats:
    for p in glob.glob(pat, recursive=True):
      try: C.append((os.path.getmtime(p),p))
      except FileNotFoundError: pass
  return sorted(C,key=lambda t:t[0],reverse=True)[0][1] if C else None
ts=datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
src=newest(["analysis/**/logB_receipt_*.json",".tau_ledger/**/logB_receipt_*.json"])
val=0.0
if src:
  try:
    d=json.load(open(src,"r",encoding="utf-8"))
    for k in ("logB","B","value"): val=float(d.get(k,0.0) or 0.0)
  except Exception: pass
A=Path(f"analysis/freed/logB_atlas_A_{ts}.json")
B=Path(f"analysis/freed/logB_atlas_B_{ts}.json")
A.parent.mkdir(parents=True,exist_ok=True)
json.dump({"logB":val,"atlas":"A","note":"stub atlas A from base logB"},open(A.with_suffix(".json.tmp"),"w",encoding="utf-8"),indent=2); os.replace(A.with_suffix(".json.tmp"),A)
json.dump({"logB":val,"atlas":"B","note":"stub atlas B from base logB"},open(B.with_suffix(".json.tmp"),"w",encoding="utf-8"),indent=2); os.replace(B.with_suffix(".json.tmp"),B)
print(A.as_posix()); print(B.as_posix())
