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
def load_logB():
    p=newest(["analysis/**/logB_receipt_*.json",".tau_ledger/**/logB_receipt_*.json"])
    if not p: return None
    try:
        with open(p,"r",encoding="utf-8") as f:
            d=json.load(f);
            for k in ("logB","B","value"):
                if k in d and isinstance(d[k],(int,float)): return abs(float(d[k]))
    except Exception:
        pass
    return None
def main():
    ts=datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
    base=load_logB()
    Vpre = float(base) if base is not None else 0.0
    Vpost = float(base) if base is not None else 0.0
    pre=Path(f"analysis/freed/volume_pre_{ts}.json")
    post=Path(f"analysis/freed/volume_post_{ts}.json")
    pre.parent.mkdir(parents=True, exist_ok=True)
    with open(pre.with_suffix(".json.tmp"),"w",encoding="utf-8") as f: json.dump({"volume":Vpre,"note":"volume_probe neutral (base from |logB| or 0)"},f,indent=2)
    os.replace(pre.with_suffix(".json.tmp"), pre)
    with open(post.with_suffix(".json.tmp"),"w",encoding="utf-8") as f: json.dump({"volume":Vpost,"note":"volume_probe neutral (base from |logB| or 0)"},f,indent=2)
    os.replace(post.with_suffix(".json.tmp"), post)
    print(pre.as_posix())
    print(post.as_posix())
if __name__=="__main__": import sys; sys.exit(main())
