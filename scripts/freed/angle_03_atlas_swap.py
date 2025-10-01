#!/usr/bin/env python3
import json, os, glob, datetime
from pathlib import Path

def newest(pats):
    c=[]
    for pat in pats:
        for p in glob.glob(pat, recursive=True):
            try: c.append((os.path.getmtime(p), p))
            except FileNotFoundError: pass
    return sorted(c, key=lambda t:t[0], reverse=True)[0][1] if c else None

def load_num(path):
    try:
        with open(path,"r",encoding="utf-8") as f: d=json.load(f)
    except Exception: return None
    for k in ("logB","B","value"):
        v=d.get(k)
        if isinstance(v,(int,float)): return float(v)
        if isinstance(v,str):
            try: return float(v)
            except Exception: pass
    return None

def emit(out,payload):
    out.parent.mkdir(parents=True, exist_ok=True)
    tmp=out.with_suffix(out.suffix+".tmp")
    with open(tmp,"w",encoding="utf-8") as f: json.dump(payload,f,indent=2,sort_keys=True)
    os.replace(tmp,out)

def main():
    ts=datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
    out=Path(f"analysis/freed/atlas_swap_{ts}.json")
    a=newest(["analysis/**/logB_atlas_A_*.json",".tau_ledger/**/logB_atlas_A_*.json"])
    b=newest(["analysis/**/logB_atlas_B_*.json",".tau_ledger/**/logB_atlas_B_*.json"])
    status="pending"; method="pending"; note="need both A and B atlas receipts"; delta=None; ratio=None
    va=load_num(a) if a else None
    vb=load_num(b) if b else None
    if a and b:
        if va is not None and vb is not None:
            status="ok"; method="atlas_swap_diff_ratio"; delta=vb-va
            ratio=(vb/va) if (va is not None and abs(va)>1e-15) else None
            note=""
        else:
            note="could not parse numeric logB values from A/B"
    inputs={"atlas_A":a,"atlas_B":b}
    inputs_norm={k:(Path(v).as_posix() if isinstance(v,str) else v) for k,v in inputs.items()}
    payload={"angle":"03_atlas_swap","timestamp":ts,"status":status,"method":method,"delta":delta,"ratio":ratio,"inputs":inputs_norm,"note":note}
    emit(out,payload); print(out.as_posix())
if __name__=="__main__": import sys; sys.exit(main())
