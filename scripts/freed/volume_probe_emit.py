#!/usr/bin/env python3
import json, os, glob, datetime; from pathlib import Path
def newest(p):
  c=[]; [c.append((os.path.getmtime(x),x)) for pat in p for x in glob.glob(pat, recursive=True) if os.path.exists(x)]
  return sorted(c, key=lambda t:t[0], reverse=True)[0][1] if c else None
def load_abs_logB():
  p=newest(["analysis/**/logB_receipt_*.json",".tau_ledger/**/logB_receipt_*.json"]);
  if not p: return None
  try:
    d=json.load(open(p,"r",encoding="utf-8"))
    for k in ("logB","B","value"):
      if isinstance(d.get(k), (int,float)): return abs(float(d[k]))
  except Exception: pass; return None
ts=datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
base=load_abs_logB(); V=float(base) if base is not None else 0.0
pre=Path(f"analysis/freed/volume_pre_{ts}.json"); post=Path(f"analysis/freed/volume_post_{ts}.json")
pre.parent.mkdir(parents=True, exist_ok=True)
json.dump({"volume":V,"note":"neutral volume from |logB| or 0"}, open(pre.with_suffix(".json.tmp"),"w",encoding="utf-8"), indent=2); os.replace(pre.with_suffix(".json.tmp"), pre)
json.dump({"volume":V,"note":"neutral volume from |logB| or 0"}, open(post.with_suffix(".json.tmp"),"w",encoding="utf-8"), indent=2); os.replace(post.with_suffix(".json.tmp"), post)
print(pre.as_posix()); print(post.as_posix())
