#!/usr/bin/env python3
import os, json, math

def rd(x):
    return None if x is None else float(x)

def envfloat(name, default):
    raw = os.environ.get(name, "")
    raw = raw.strip() if isinstance(raw, str) else ""
    return float(raw) if raw else default

passport = json.load(open(".tau_ledger/physics/passport.json","r",encoding="utf-8")) if os.path.exists(".tau_ledger/physics/passport.json") else {}

M_phys = rd(passport.get("gpu",{}).get("mem_total_bytes")) or rd(passport.get("cpu",{}).get("mem_total_bytes")) or 4.0e9
beta   = rd(passport.get("io",{}).get("beta_sustained_bytes_per_s")) or 2.0e9
IO_FRAC = float(os.environ.get("IO_FRAC","0") or "0")
c_time = rd(passport.get("coefficients",{}).get("c_time")) or 1e-9
c_energy = rd(passport.get("coefficients",{}).get("c_energy")) or 0.0
c_mem = rd(passport.get("coefficients",{}).get("c_mem")) or 1.0
E0 = rd(passport.get("coefficients",{}).get("E0")) or 0.0

# model coefficients (simple defaults; tune later)
s0=0.0; s1=8.0; s2=8.0
w1=3.0; w2=5.0
A=1.0; sigma=0.08

L_max   = envfloat("L_MAX", 2.0)
E_max   = envfloat("E_MAX", 50.0)
# empty M_MAX => 80% of physical memory
M_max   = envfloat("M_MAX", M_phys*0.8) if os.environ.get("M_MAX","").strip() else M_phys*0.8
EPS_MAX = envfloat("EPS_MAX", 1e-6)
TAU_STAR= envfloat("TAU_STAR", 12.0)

def S(n,k): return s0 + s1*n + s2*k*n
def W(n,k): return w1*n + w2*k*n
def eps_of(k): return A*math.exp(-sigma*k)

k_min = math.ceil((1.0/sigma)*math.log(max(A/EPS_MAX,1.0)))

def n_max_for(k):
    cap = M_max/max(c_mem,1e-9) - s0
    den = (s1 + s2*k)
    return max(0, int(cap/den))

k = max(1, int(k_min))
n = n_max_for(k)

def predict(n,k):
    work = W(n,k)
    T_hat = c_time*work
    E_hat = c_energy*work + E0
    M_hat = c_mem*S(n,k)
    X = S(n,k)
    T_io = X/max(beta,1.0)
    return max(T_hat,T_io), E_hat, M_hat

if n <= 0:
    raise SystemExit("[select] memory guard left no room; relax k (via EPS_MAX) or increase M_MAX")

while n>0:
    T_pred,E_pred,M_pred = predict(n,k)
print(f"[select/debug] c_time={c_time} IO_FRAC={IO_FRAC} beta={beta} W={(w1+w2*k)*n} S={S(n,k)}")
    if T_pred<=L_max and (E_pred<=E_max or c_energy==0.0) and M_pred<=M_max:
        break
    n = int(n*0.9)

if n<=0:
    raise SystemExit("[select] no feasible (n,k) under budgets; relax budgets or adjust models")

pre={
  "selected": {"n": int(n), "k": int(k)},
  "budgets": {"L_max": L_max, "E_max": E_max, "M_max": M_max, "EPS_MAX": EPS_MAX, "TAU_STAR": TAU_STAR},
  "predicted": {"T": predict(n,k)[0], "E": predict(n,k)[1], "M": predict(n,k)[2], "eps": eps_of(k)},
  "models": {"S": {"s0":s0,"s1":s1,"s2":s2}, "W":{"w1":w1,"w2":w2}, "error":{"A":A,"sigma":sigma}},
  "passport_ref": ".tau_ledger/physics/passport.json"
}
open(".tau_ledger/physics/pre_cert.json","w",encoding="utf-8").write(json.dumps(pre,indent=2))
print(f"[select] chose n={n} k={k}  T^={pre['predicted']['T']:.3f}  M^={pre['predicted']['M']/2**30:.3f} GiB  eps^={pre['predicted']['eps']:.3e}")
