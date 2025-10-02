#!/usr/bin/env python3
"""
HEO ML Inference

Usage:
  python ci/heo/research/ml_infer.py --model ci/heo/research/models/ml_predictor_linear.json \
         --sequence ci/data/sequences/periodic_7_0010010.json

Outputs JSON:
{
  "predicted_H": ...,
  "exact_H": ... (if computable),
  "abs_error": ... (if exact),
  "features": {...},
  "columns": [...],
  "weights": [...]
}
"""
import json, argparse, math
from typing import List, Dict
try:
    import numpy as np
except Exception as e:
    print(json.dumps({"error":"numpy required","detail":str(e)})); raise

def load_sequence(path: str) -> List[int]:
    obj = json.load(open(path))
    if obj.get("kind") == "periodic" and "pattern" in obj:
        return obj["pattern"]
    if obj.get("kind") == "explicit" and "values" in obj:
        # allow 0/1 values directly
        return obj["values"]
    # fallback: try generic "pattern"
    if "pattern" in obj:
        return obj["pattern"]
    raise SystemExit(f"unsupported sequence format in {path}")

def autocorr01(patt: List[int], lag: int) -> float:
    T = len(patt)
    if lag <= 0 or lag >= T: return 0.0
    x = np.array(patt, dtype=float)
    mu = x.mean()
    x0 = x - mu
    num = float(np.dot(x0, np.roll(x0, -lag)))
    den = float(np.dot(x0, x0) + 1e-12)
    return num/den

def run_stats(patt: List[int]):
    runs = []
    cur = patt[0]; cnt = 1
    for v in patt[1:]:
        if v == cur: cnt += 1
        else: runs.append(cnt); cur=v; cnt=1
    runs.append(cnt)
    arr = np.array(runs, dtype=float)
    return len(runs), float(arr.mean()), float(arr.var())

def lowfreq_energy(patt: List[int], K=3):
    x = np.array(patt, dtype=float)
    X = np.fft.rfft(x)
    mags = np.abs(X)[1:K+1] / (len(x)+1e-12)
    out = [0.0,0.0,0.0]
    for i,m in enumerate(mags[:3]): out[i] = float(m)
    return out

def mod_profile(patt: List[int], mod: int):
    T = len(patt); prof=[]
    for r in range(mod):
        idx = list(range(r, T, mod))
        prof.append(sum(patt[i] for i in idx)/len(idx) if idx else 0.0)
    return prof

def features(patt: List[int]) -> Dict[str, float]:
    T = len(patt)
    ac1 = autocorr01(patt, 1)
    ac2 = autocorr01(patt, 2)
    nr, rmean, rvar = run_stats(patt)
    dft1,dft2,dft3 = lowfreq_energy(patt, K=3)
    m3 = mod_profile(patt, 3)
    m4 = mod_profile(patt, 4)
    return {
        "T": float(T),
        "ac1": ac1, "ac2": ac2,
        "runs": float(nr), "run_mean": rmean, "run_var": rvar,
        "dft1": dft1, "dft2": dft2, "dft3": dft3,
        "mod3_0": m3[0], "mod3_1": m3[1], "mod3_2": m3[2],
        "mod4_0": m4[0], "mod4_1": m4[1], "mod4_2": m4[2], "mod4_3": m4[3],
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", required=True)
    ap.add_argument("--sequence", required=True)
    args = ap.parse_args()

    model = json.load(open(args.model))
    patt = load_sequence(args.sequence)
    f = features(patt)

    cols = model["columns"]
    w = np.array(model["weights"], dtype=float)
    x = [1.0] + [f[c] for c in cols if c in f]  # bias + feature order from model
    X = np.array(x, dtype=float)
    pred = float(np.dot(X, w))

    exact = None
    if len(set(patt)) <= 2 and all(v in (0,1) for v in patt):
        exact = sum(patt)/len(patt)

    out = {
        "predicted_H": pred,
        "exact_H": exact,
        "abs_error": (abs(pred - exact) if exact is not None else None),
        "features": f,
        "columns": cols,
        "weights": model["weights"]
    }
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
