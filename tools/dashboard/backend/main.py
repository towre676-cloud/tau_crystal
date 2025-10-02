#!/usr/bin/env python3
"""
HEO Experimental Dashboard — FastAPI backend (JSON-focused for CI)
Endpoints:
  POST /compute_heo      { "pattern": [0,1,0,...] , "d": 2, "k": 0 }
  POST /compute_spectrum { "pattern": [...], "k_min": -5, "k_max": 5, "ds": [2,3,5,7] }
"""
from __future__ import annotations
from fastapi import FastAPI
from pydantic import BaseModel, conlist
from typing import List, Optional

app = FastAPI(title="HEO Dashboard", version="0.1.0")

class SequencePayload(BaseModel):
    pattern: conlist(int, min_items=1)
    d: Optional[int] = 2
    k: Optional[int] = 0

class SpectrumPayload(BaseModel):
    pattern: conlist(int, min_items=1)
    k_min: int = -5
    k_max: int = 5
    ds: Optional[List[int]] = None

@app.post("/compute_heo")
def compute_heo(payload: SequencePayload):
    patt = payload.pattern
    T = len(patt)
    ones = sum(1 for x in patt if x)
    H = ones / T
    # convergence trace over one period (demo)
    s = 0
    trace = []
    for n, x in enumerate(patt, start=1):
        s += 1 if x else 0
        trace.append({"n": n, "density": s / n})
    return {
        "period": T,
        "ones": ones,
        "H": H,
        "d": payload.d,
        "k": payload.k,
        "trace": trace
    }

@app.post("/compute_spectrum")
def compute_spectrum(payload: SpectrumPayload):
    patt = payload.pattern
    T = len(patt)
    H = sum(1 for x in patt if x) / T
    ds = payload.ds if payload.ds else [2, 3, 5, 7]
    k_min, k_max = payload.k_min, payload.k_max
    heatmap = [{"d": d, "k": k, "H": H}
               for d in ds for k in range(k_min, k_max + 1)]
    return {
        "period": T,
        "H_baseline": H,
        "grid": {"k_min": k_min, "k_max": k_max, "ds": ds},
        "heatmap": heatmap
    }

if __name__ == "__main__":
    # Optional local run: uvicorn tools.dashboard.backend.main:app --reload
    import uvicorn
    uvicorn.run(app, host="127.0.0.1", port=8000)
