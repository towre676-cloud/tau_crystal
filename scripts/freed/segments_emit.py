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
outa=Path(f"analysis/freed/logB_segment_a_{ts}.json")
outb=Path(f"analysis/freed/logB_segment_b_{ts}.json")
outw=Path(f"analysis/freed/logB_segment_whole_{ts}.json")
for p in (outa,outb,outw): p.parent.mkdir(parents=True,exist_ok=True)
json.dump({"logB":val/2,"note":"stub segment a"},open(outa.with_suffix(".json.tmp"),"w",encoding="utf-8"),indent=2); os.replace(outa.with_suffix(".json.tmp"),outa)
json.dump({"logB":val/2,"note":"stub segment b"},open(outb.with_suffix(".json.tmp"),"w",encoding="utf-8"),indent=2); os.replace(outb.with_suffix(".json.tmp"),outb)
json.dump({"logB":val,"note":"stub whole (a+b)"},open(outw.with_suffix(".json.tmp"),"w",encoding="utf-8"),indent=2); os.replace(outw.with_suffix(".json.tmp"),outw)
print(outa.as_posix()); print(outb.as_posix()); print(outw.as_posix())
