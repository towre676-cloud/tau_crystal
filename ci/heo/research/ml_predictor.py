#!/usr/bin/env python3
"""
HEO ML Predictor (lightweight)

- Generates synthetic binary periodic sequences
- Extracts simple, theory-guided features (autocorr, run stats, low-frequency DFT)
- Fits a ridge-regularized linear model (closed form via numpy) to predict H = mean of X
- Evaluates MAE on held-out set
- Saves learned weights to JSON for reproducibility
"""
import json, argparse, math, os, random
from statistics import mean
from typing import List, Dict, Tuple
try:
    import numpy as np
except Exception as e:
    print(json.dumps({"error": "numpy required", "detail": str(e)}))
    raise

def set_seed(seed: int = 1337):
    random.seed(seed)
    np.random.seed(seed % (2**32 - 1))

def gen_periodic(T: int, density: float) -> List[int]:
    """Generate a periodic 0/1 pattern of length T with approx given density."""
    k = int(round(density * T))
    patt = [1]*k + [0]*(T-k)
    random.shuffle(patt)
    return patt

def autocorr01(patt: List[int], lag: int) -> float:
    T = len(patt)
    if lag <= 0 or lag >= T: return 0.0
    x = np.array(patt, dtype=float)
    mu = x.mean()
    x0 = x - mu
    num = np.dot(x0, np.roll(x0, -lag))
    den = np.dot(x0, x0) + 1e-12
    return float(num/den)

def run_stats(patt: List[int]) -> Tuple[int, float, float]:
    """Return (#runs, avg_run_length, var_run_length) for runs of equal bits."""
    runs = []
    cur = patt[0]; cnt = 1
    for v in patt[1:]:
        if v == cur:
            cnt += 1
        else:
            runs.append(cnt)
            cur = v; cnt = 1
    runs.append(cnt)
    arr = np.array(runs, dtype=float)
    return len(runs), float(arr.mean()), float(arr.var())

def lowfreq_energy(patt: List[int], K: int = 3) -> List[float]:
    """First K non-DC magnitudes of real DFT (normalized)."""
    x = np.array(patt, dtype=float)
    X = np.fft.rfft(x)
    mags = np.abs(X)[1:K+1] / (len(x)+1e-12)
    return [float(m) for m in mags]

def mod_profile(patt: List[int], mod: int) -> List[float]:
    """Average of pattern on each residue class mod 'mod' (rotational features)."""
    T = len(patt)
    prof = []
    for r in range(mod):
        idx = list(range(r, T, mod))
        if idx:
            prof.append(sum(patt[i] for i in idx)/len(idx))
        else:
            prof.append(0.0)
    return prof

def features(patt: List[int]) -> Dict[str, float]:
    T = len(patt)
    H = sum(patt)/T
    ac1 = autocorr01(patt, 1)
    ac2 = autocorr01(patt, 2)
    nr, rmean, rvar = run_stats(patt)
    dft = lowfreq_energy(patt, K=3)
    mod3 = mod_profile(patt, 3)
    mod4 = mod_profile(patt, 4)
    # IMPORTANT: do not leak H directly as a feature; the model should infer it
    feats = {
        "T": float(T),
        "ac1": ac1,
        "ac2": ac2,
        "runs": float(nr),
        "run_mean": rmean,
        "run_var": rvar,
        "dft1": dft[0], "dft2": dft[1] if len(dft)>1 else 0.0, "dft3": dft[2] if len(dft)>2 else 0.0,
        "mod3_0": mod3[0], "mod3_1": mod3[1], "mod3_2": mod3[2],
        "mod4_0": mod4[0], "mod4_1": mod4[1], "mod4_2": mod4[2], "mod4_3": mod4[3],
    }
    return feats

def synth_corpus(n_train=400, n_test=200, T_choices=(7,9,11,13), dens_grid=None):
    if dens_grid is None:
        dens_grid = [i/10 for i in range(1,10)]
    train, test = [], []
    for _ in range(n_train):
        T = random.choice(T_choices)
        d = random.choice(dens_grid)
        patt = gen_periodic(T, d)
        train.append((patt, sum(patt)/T))
    for _ in range(n_test):
        T = random.choice(T_choices)
        d = random.choice(dens_grid)
        patt = gen_periodic(T, d)
        test.append((patt, sum(patt)/T))
    return train, test

def design_matrix(samples):
    X_list, y_list, keys = [], [], None
    for patt, H in samples:
        f = features(patt)
        if keys is None:
            keys = sorted(f.keys())
        x = [f[k] for k in keys]
        X_list.append(x)
        y_list.append(H)
    X = np.array(X_list, dtype=float)
    y = np.array(y_list, dtype=float)
    # add bias column
    X = np.concatenate([np.ones((X.shape[0],1)), X], axis=1)
    cols = ["bias"] + keys
    return X, y, cols

def ridge_fit(X, y, lam=1e-3):
    d = X.shape[1]
    A = X.T @ X + lam * np.eye(d)
    b = X.T @ y
    w = np.linalg.solve(A, b)
    return w

def mae(pred, y):
    return float(np.mean(np.abs(pred - y)))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1337)
    ap.add_argument("--train", action="store_true")
    ap.add_argument("--eval", action="store_true")
    ap.add_argument("--save", default="ci/heo/research/models/ml_predictor_linear.json")
    ap.add_argument("--lam", type=float, default=1e-3)
    ap.add_argument("--target_mae", type=float, default=0.02)
    args = ap.parse_args()

    set_seed(args.seed)
    train, test = synth_corpus()

    Xtr, ytr, cols = design_matrix(train)
    Xte, yte, _    = design_matrix(test)

    w = ridge_fit(Xtr, ytr, lam=args.lam)
    pred_tr = Xtr @ w
    pred_te = Xte @ w

    out = {
        "train_mae": mae(pred_tr, ytr),
        "test_mae":  mae(pred_te, yte),
        "dof": int(Xtr.shape[1]),
        "lambda": args.lam,
        "columns": cols,
        "weights": [float(x) for x in w.tolist()]
    }

    if args.train or args.eval:
        print(json.dumps(out, indent=2))

    # Save model
    os.makedirs(os.path.dirname(args.save), exist_ok=True)
    with open(args.save, "w") as f:
        json.dump(out, f, indent=2)

    # Optional assertion on generalization
    if args.eval:
        assert out["test_mae"] <= args.target_mae + 1e-9, f"MAE too high: {out['test_mae']:.4f} > {args.target_mae:.4f}"

if __name__ == "__main__":
    main()
