#!/usr/bin/env python3
import json, os, glob, datetime; from pathlib import Path
def newest(p):
  c=[]; [c.append((os.path.getmtime(x),x)) for pat in p for x in glob.glob(pat, recursive=True) if os.path.exists(x)]
  return sorted(c, key=lambda t:t[0], reverse=True)[0][1] if c else None
def num(p):
  try: d=json.load(open(p,"r",encoding="utf-8"))
  except Exception: return None
  for k in ("logB","B","value"):
    v=d.get(k);
    if isinstance(v,(int,float)): return float(v)
  return None
ts=datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
out=Path(f"analysis/freed/relative_functor_{ts}.json")
a=newest(["analysis/**/logB_segment_a_*.json",".tau_ledger/**/logB_segment_a_*.json"])
b=newest(["analysis/**/logB_segment_b_*.json",".tau_ledger/**/logB_segment_b_*.json"])
w=newest(["analysis/**/logB_segment_whole_*.json",".tau_ledger/**/logB_segment_whole_*.json"])
status="pending"; method="pending"; additivity=None; residual=None; note="need a,b,whole"
if a and b and w:
  va=num(a); vb=num(b); vw=num(w)
  if None not in (va,vb,vw): residual=vw-(va+vb); additivity=(abs(residual)<=1e-12); status="ok"; method="logB_additivity"; note=""
inputs={"segment_a":a,"segment_b":b,"segment_whole":w}; inputs_norm={k:(Path(v).as_posix() if isinstance(v,str) else v) for k,v in inputs.items()}
out.parent.mkdir(parents=True, exist_ok=True)
json.dump({"angle":"01_relative_functor","timestamp":ts,"status":status,"method":method,"additivity":additivity,"residual":residual,"inputs":inputs_norm,"note":note}, open(out.with_suffix(".json.tmp"),"w",encoding="utf-8"), indent=2, sort_keys=True); os.replace(out.with_suffix(".json.tmp"), out)
print(out.as_posix())
