#!/usr/bin/env python3
import json, os, glob, datetime; from pathlib import Path
def newest(p):
  c=[]; [c.append((os.path.getmtime(x),x)) for pat in p for x in glob.glob(pat, recursive=True) if os.path.exists(x)]
  return sorted(c, key=lambda t:t[0], reverse=True)[0][1] if c else None
def loadnum(p):
  try: d=json.load(open(p,"r",encoding="utf-8"))
  except Exception: return None
  for k in ("logB","B","value"):
    v=d.get(k);
    if isinstance(v,(int,float)): return float(v)
  return None
ts=datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
out=Path(f"analysis/freed/atlas_swap_{ts}.json")
a=newest(["analysis/**/logB_atlas_A_*.json",".tau_ledger/**/logB_atlas_A_*.json"])
b=newest(["analysis/**/logB_atlas_B_*.json",".tau_ledger/**/logB_atlas_B_*.json"])
status="pending"; method="pending"; delta=None; ratio=None; note="need A and B atlas receipts"
if a and b:
  va=loadnum(a); vb=loadnum(b)
  if va is not None and vb is not None:
    status="ok"; method="atlas_swap_diff_ratio"; delta=vb-va; ratio=(vb/va) if abs(va)>1e-15 else None; note=""
  else: note="could not parse numeric logB values"
inputs={"atlas_A":a,"atlas_B":b}; inputs_norm={k:(Path(v).as_posix() if isinstance(v,str) else v) for k,v in inputs.items()}
out.parent.mkdir(parents=True, exist_ok=True)
json.dump({"angle":"03_atlas_swap","timestamp":ts,"status":status,"method":method,"delta":delta,"ratio":ratio,"inputs":inputs_norm,"note":note}, open(out.with_suffix(".json.tmp"),"w",encoding="utf-8"), indent=2, sort_keys=True); os.replace(out.with_suffix(".json.tmp"), out)
print(out.as_posix())
