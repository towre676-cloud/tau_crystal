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
lvl=0.0
if src:
  try:
    d=json.load(open(src,"r",encoding="utf-8"))
    for k in ("logB","B","value"): lvl+=abs(float(d.get(k,0.0) or 0.0))
  except Exception: pass
out=Path(f"analysis/freed/tmf_level_{ts}.json")
out.parent.mkdir(parents=True,exist_ok=True)
json.dump({"dlogB":lvl,"note":"stub tmf level from |logB|"},open(out.with_suffix(".json.tmp"),"w",encoding="utf-8"),indent=2); os.replace(out.with_suffix(".json.tmp"),out)
print(out.as_posix())
