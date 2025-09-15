import sys, os, json, numpy as np, mpmath as mp
from pathlib import Path
sys.path.append("scripts")
from discovery.local_factors import load_params, satake_from_ap
from discovery.euler_products import L_GL2_from_ap, L_Sym2_from_satake
from discovery.completed_L import complete_L
mp.mp.dps=80
out = Path(".tau_ledger/discovery/confirm_double_zero.json")
plotdir = Path(".tau_ledger/discovery/plots"); plotdir.mkdir(parents=True, exist_ok=True)
params = load_params(); ap=params["ap"]; N=params["N"]; k=params["k"]; eps=params["epsilon"]; Q=params["Q"]; gamma=params["gamma"]
if not ap:
    out.write_text(json.dumps({"confirm":{"flag":False,"reason":"no Hecke a_p found","params":params}},sort_keys=True,separators=(",",":"))+"\n", encoding="utf-8")
    print(out.as_posix())
    raise SystemExit
L_gl2 = L_GL2_from_ap(ap,k,N)
satake={}
for p in sorted(ap.keys()):
    ab = satake_from_ap(ap,p,k)
    if ab: satake[p]=ab
L_sym2 = L_Sym2_from_satake(satake)
def Lam_gl2(s): return complete_L(s,L_gl2,Q,gamma,eps)
def Lam_sym2(s): return complete_L(s,L_sym2,Q**2,gamma,1)
ts = np.linspace(0.1,8.0,200)
sym_scores  = [float(abs(Lam_gl2(0.5+1j*t) - eps*mp.conj(Lam_gl2(0.5-1j*t)))) for t in ts]
sym2_scores = [float(abs(Lam_sym2(0.5+1j*t) -    mp.conj(Lam_sym2(0.5-1j*t)))) for t in ts]
def fR(t): return float(mp.re(Lam_gl2(0.5+1j*t)))
zeros_gl2=[]; grid=np.linspace(0.1,8.0,400); last=None
for t in grid:
    v=fR(t)
    if last is not None and (v==0 or v*last<0): zeros_gl2.append(float(t))
    last=v
outside_hits=[]
def scan_rect(x0,x1,y0,y1,dx=0.05,dy=0.05):
    xs=np.arange(x0, x1+1e-12, dx)
    ys=np.arange(y0, y1+1e-12, dy)
    for x in xs:
        for y in ys:
            val = abs(L_sym2(complex(float(x),float(y))))
            if val < 1e-6: outside_hits.append({"re":float(x),"im":float(y),"abs":float(val)})
scan_rect(1.1,3.0,0.0,3.0,0.05,0.05)
scan_rect(-2.0,-0.1,0.0,3.0,0.05,0.05)
obj={"confirm":{
    "params":{"N":N,"k":k,"epsilon":eps,"Q":Q,"gamma":gamma,"num_ap":len(ap)},
    "symmetry_scores":{"gl2_max":max(sym_scores),"sym2_max":max(sym2_scores)},
    "critical_line_zeros_gl2":zeros_gl2,
    "sym2_outside_hits":outside_hits
}}
out.write_text(json.dumps(obj,sort_keys=True,separators=(",",":"))+"\n", encoding="utf-8")
print(out.as_posix())
