#!/usr/bin/env python3
import json,sys,os,glob,datetime
from pathlib import Path

def newest(patterns):
    cands=[]
    for pat in patterns:
        for p in glob.glob(pat, recursive=True):
            try:
                cands.append((os.path.getmtime(p), p))
            except FileNotFoundError:
                pass
    if not cands: return None
    cands.sort(key=lambda x: x[0], reverse=True)
    return cands[0][1]

def safe_load(path):
    try:
        with open(path,"r",encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return None

def emit(out_path, payload):
    out_path.parent.mkdir(parents=True, exist_ok=True)
    tmp=out_path.with_suffix(out_path.suffix+".tmp")
    with open(tmp,"w",encoding="utf-8") as f:
        json.dump(payload,f,indent=2,sort_keys=True)
    os.replace(tmp,out_path)

def main():
    ts=datetime.datetime.now(datetime.UTC).strftime("%Y%m%dT%H%M%SZ")
    out=Path(f"analysis/freed/relative_index_{ts}.json")
    # Inputs: prefer volume pre/post; else fall back to sigma/logB; else proxy
    pre=newest([
        "analysis/freed/volume_pre_*.json",
        "analysis/*/volume_pre_*.json",
        ".tau_ledger/**/volume_pre_*.json"
    ])
    post=newest([
        "analysis/freed/volume_post_*.json",
        "analysis/*/volume_post_*.json",
        ".tau_ledger/**/volume_post_*.json"
    ])
    sigma=newest([
        "analysis/freed/sigma_leaf_*.json",
        "analysis/*/sigma_leaf_*.json",
        ".tau_ledger/**/sigma_leaf_*.json"
    ])
    logB=newest([
        "analysis/freed/logB_receipt_*.json",
        "analysis/*/logB_receipt_*.json",
        ".tau_ledger/**/logB_receipt_*.json"
    ])

    method="proxy"; status="proxy"; value=0.0; note=""
    inputs={"volume_pre":pre,"volume_post":post,"sigma_leaf":sigma,"logB_receipt":logB}

    # Strategy 1: volume-based relative index (preferred)
    if pre and post:
        dpre=safe_load(pre) or {}
        dpost=safe_load(post) or {}
        Vpre=float(dpre.get("volume", dpre.get("V", 0.0)) or 0.0)
        Vpost=float(dpost.get("volume", dpost.get("V", 0.0)) or 0.0)
        denom=Vpre if abs(Vpre)>1e-15 else 1.0
        value=(Vpost - Vpre)/denom
        method="volume_diff_norm"; status="ok"; note="(Vpost-Vpre)/Vpre with fallback denom if needed"

    # Strategy 2: sigma/logB proxy
    elif sigma and logB:
        ds=safe_load(sigma) or {}
        dl=safe_load(logB) or {}
        s=float(ds.get("sigma", ds.get("Σ", 0.0)) or 0.0)
        b=float(dl.get("logB", dl.get("B", 0.0)) or 0.0)
        scale=1.0 if abs(b)<1e-12 else 1.0/abs(b)
        value=s*scale
        method="sigma_over_abs_logB"; status="ok"; note="proxy via Σ scaled by |logB|^{-1}"

    # Strategy 3: hard proxy
    else:
        note="no suitable inputs found; emitting neutral proxy 0.0"

    payload={
        "angle":"10_relative_index",
        "timestamp": ts,
        "method": method,
        "status": status,
        "value": value,
        "units":"arb",
        "inputs": inputs,
        "note": note
    }
    emit(out, payload)
    print(str(out))

if __name__=="__main__":
    sys.exit(main())
