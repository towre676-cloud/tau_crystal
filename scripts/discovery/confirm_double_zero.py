import json, os
from pathlib import Path
import numpy as np
import mpmath as mp

mp.mp.dps = 80

# Local params (stable-first)
import importlib.util, sys
sys.path.append("scripts")
from discovery.local_factors import load_params
from discovery.euler_products import L_GL2_from_ap, L_Sym2_from_satake
from discovery.completed_L import complete_L

OUT = Path(".tau_ledger/discovery/confirm_double_zero.json")
PLOT = Path(".tau_ledger/discovery/plots"); PLOT.mkdir(parents=True, exist_ok=True)

def turing_count(Lam, T, dt=0.01):
    """Crude argument-principle count: Δ arg Λ(1/2+it) / π over [0,T]."""
    t = 0.0; last = None; total = 0.0
    while t <= T:
        z = 0.5 + 1j*t
        val = Lam(z)
        a = mp.arg(val)
        if last is not None:
            da = a - last
            # unwrap
            while da > mp.pi: da -= 2*mp.pi
            while da < -mp.pi: da += 2*mp.pi
            total += da
        last = a
        t += dt
    return abs(total/mp.pi)

def scan_critical_zeros(Lam, t_grid):
    zs = []
    fR = lambda t: float(mp.re(Lam(0.5+1j*t)))
    last = None; last_t=None
    for t in t_grid:
        v = fR(t)
        if last is not None and v == 0 or (last is not None and v*last < 0):
            # refine with Brent on Re(Λ) along the line
            try:
                root = mp.findroot(lambda x: mp.re(Lam(0.5+1j*x)), (last_t, t))
                zs.append(float(root))
            except:  # fallback midpoint
                zs.append(float(0.5*(last_t+t)))
        last, last_t = v, t
    return sorted(zs)

def scan_sym2_outside(L_sym2, rects, step=0.05, thresh=1e-8):
    hits = []
    for (x0,x1,y0,y1) in rects:
        xs = np.arange(x0, x1+1e-12, step)
        ys = np.arange(y0, y1+1e-12, step)
        for x in xs:
            for y in ys:
                val = abs(L_sym2(complex(float(x), float(y))))
                if val < thresh:
                    hits.append({"re": float(x), "im": float(y), "abs": float(val)})
    return hits

def main():
    P = load_params()
    ap, sat = P["ap"], P["satake"]
    N, k, eps, Q, gamma = P["N"], P["k"], P["epsilon"], P["Q"], P["gamma"]

    if not ap and not sat:
        OUT.write_text(json.dumps({"confirm":{"flag":False,"reason":"no Hecke/Satake data","params":P}},sort_keys=True,separators=(",",":"))+"\n", encoding="utf-8")
        print(OUT.as_posix()); return

    # Build L(s) and Λ(s)
    L_gl2 = L_GL2_from_ap(ap, k, N)
    L_sym2 = L_Sym2_from_satake(sat if sat else {p:None for p in ap.keys()})
    # heuristic archimedean shift: use (k-1)/2 for holomorphic GL(2);  shift  = (k+1)/2 for Sym^2
    shift_gl2  = (k-1)/2 if k else 0.0
    shift_sym2 = (k+1)/2 if k else 0.0
    Lam_gl2  = lambda s: complete_L(s, L_gl2,  Q,   gamma, eps, shift_gl2)
    Lam_sym2 = lambda s: complete_L(s, L_sym2, Q**2, gamma, 1,   shift_sym2)

    # Symmetry checks (max deviation)
    ts = np.linspace(0.25, 10.0, 300)
    sym_gl2  = [abs(Lam_gl2(0.5+1j*t) - eps*mp.conj(Lam_gl2(0.5-1j*t))) for t in ts]
    sym_sym2 = [abs(Lam_sym2(0.5+1j*t) -     mp.conj(Lam_sym2(0.5-1j*t))) for t in ts]
    sym_scores = {"gl2_max": float(max(sym_gl2)), "sym2_max": float(max(sym_sym2))}

    # Turing count
    count = float(turing_count(Lam_gl2, T=8.0, dt=0.01))

    # Critical-line zeros (Brent refinement on Re Λ)
    zeros_gl2 = scan_critical_zeros(Lam_gl2, t_grid=np.linspace(0.25, 10.0, 800))

    # Sym^2 outside-strip scans
    rects = [(1.1,3.0,0.0,3.0), (-2.0,-0.1,0.0,3.0)]
    hits  = scan_sym2_outside(L_sym2, rects, step=0.05, thresh=1e-8)

    obj = {
      "confirm":{
        "flag": bool(zeros_gl2) and bool(hits),
        "params":{"N":N,"k":k,"epsilon":eps,"Q":Q,"gamma":gamma,
                  "num_ap":len(ap),"num_sat":len(sat)},
        "symmetry_scores": sym_scores,
        "turing_count_0T": count,
        "critical_line_zeros_gl2": zeros_gl2,
        "sym2_outside_hits": hits,
        "notes": "Shift heuristics used; refine with exact archimedean parameters for final pass."
      }
    }
    OUT.write_text(json.dumps(obj,sort_keys=True,separators=(",",":"))+"\n", encoding="utf-8")
    print(OUT.as_posix())

    # Plots (PNG)
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    # |Λ(1/2+it)| and zeros
    mags = [float(abs(Lam_gl2(0.5+1j*t))) for t in ts]
    plt.figure()
    plt.plot(ts, mags)
    for z in zeros_gl2:
        plt.axvline(z, linestyle="--", linewidth=0.8)
    plt.xlabel("t"); plt.ylabel("|Λ(1/2+it)|"); plt.title("GL(2): magnitude with zero markers")
    plt.savefig(PLOT/"gl2_magnitude.png", dpi=160); plt.close()

    # symmetry deviation
    plt.figure()
    plt.plot(ts, [float(v) for v in sym_gl2])
    plt.xlabel("t"); plt.ylabel("|Λ(s)-ε·conj Λ(1-\\bar{s})|"); plt.title("Symmetry deviation (GL2)")
    plt.yscale("log"); plt.savefig(PLOT/"gl2_symmetry_deviation.png", dpi=160); plt.close()

    # Sym^2 heatmap (Re>1)
    xs = np.arange(1.1,3.0+1e-12,0.05); ys = np.arange(0.0,3.0+1e-12,0.05)
    Z = np.zeros((len(ys),len(xs)))
    for i,y in enumerate(ys):
        for j,x in enumerate(xs):
            Z[i,j]=float(abs(L_sym2(complex(float(x),float(y)))))
    plt.figure()
    plt.imshow(Z, origin="lower", aspect="auto", extent=[xs[0],xs[-1],ys[0],ys[-1]])
    plt.colorbar(); plt.xlabel("Re t"); plt.ylabel("Im t"); plt.title("|L(Sym^2, t)| Re>1")
    plt.savefig(PLOT/"sym2_heatmap_right.png", dpi=160); plt.close()
