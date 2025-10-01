#!/usr/bin/env python3
import json, os, glob, datetime, math
from pathlib import Path
def newest_many(pat):
  return sorted(glob.glob(pat, recursive=True), key=lambda p: os.path.getmtime(p), reverse=True)
def load_num(path, keys=("dlogB","ΔlogB","delta_logB","logB","value")):
  try:
    with open(path,"r",encoding="utf-8") as f: d=json.load(f)
  except Exception: return None
  for k in keys:
    v=d.get(k);
    if isinstance(v,(int,float)): return float(v)
  return None
def emit(out,payload):
  out.parent.mkdir(parents=True, exist_ok=True)
  tmp=out.with_suffix(out.suffix+".tmp")
  with open(tmp,"w",encoding="utf-8") as f: json.dump(payload,f,indent=2,sort_keys=True)
  os.replace(tmp,out)
def main():
  ts=datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
  out=Path(f"analysis/freed/tmf_join_dlogB_{ts}.json")
  files=newest_many("analysis/**/tmf_level_*.json") + newest_many(".tau_ledger/**/tmf_level_*.json")
  vals=[]
  for p in files[:500]:
    v=load_num(p);
    if v is not None and math.isfinite(v): vals.append(v)
  status="pending"; method="pending"; mu=None; med=None; n=len(vals); note="need tmf_level_*.json to aggregate"
  if n>0:
    status="ok"; method="tmf_dlogB_summary"; mu=sum(vals)/n; med=sorted(vals)[n//2]; note=""
  payload={"angle":"05_tmf_dlogB","timestamp":ts,"status":status,"method":method,"n":n,"mean":mu,"median":med,"note":note}
  emit(out,payload); print(out.as_posix())
if __name__=="__main__": import sys; sys.exit(main())
