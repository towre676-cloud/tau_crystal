#!/usr/bin/env python3
import os, json, math, sys

def rd(x):
    return None if x is None else float(x)

def envfloat(name, default):
    raw = os.environ.get(name, "")
    raw = raw.strip() if isinstance(raw, str) else ""
    return float(raw) if raw else default

# Load passport (optional)
passport_path = ".tau_ledger/physics/passport.json"
passport = {}
if os.path.exists(passport_path):
    try:
        passport = json.load(open(passport_path, "r", encoding="utf-8"))
    except Exception:
        passport = {}

# Physical capacities / coefficients
M_phys = rd(passport.get("gpu",{}).get("mem_total_bytes")) or rd(passport.get("cpu",{}).get("mem_total_bytes")) or 4.0e9
beta   = rd(passport.get("io",{}).get("beta_sustained_bytes_per_s")) or 2.0e9
coeff  = passport.get("coefficients", {})
c_time = rd(coeff.get("c_time")) or 1e-12         # fitted separately; default ~1e-12 for dummy kernel
c_energy = rd(coeff.get("c_energy")) or 0.0
c_mem    = rd(coeff.get("c_mem"))    or 1.0
E0 = rd(coeff.get("E0")) or 0.0

# Simple model coefficients (tune per real kernel)
s0=0.0; s1=8.0; s2=8.0      # S(n,k) = s0 + (s1 + s2 k) n   [bytes]
w1=3.0; w2=5.0              # W(n,k) = (w1 + w2 k) n        [work units]
A=1.0; sigma=0.08           # eps(k) = A * exp(-sigma k)

# Budgets + gates
L_max   = envfloat("L_MAX", 2.0)
E_max   = envfloat("E_MAX", 50.0)
M_max   = envfloat("M_MAX", M_phys*0.8) if (os.environ.get("M_MAX","").strip()=="") else envfloat("M_MAX", M_phys*0.8)
EPS_MAX = envfloat("EPS_MAX", 1e-6)
TAU_STAR= envfloat("TAU_STAR", 12.0)
IO_FRAC = envfloat("IO_FRAC", 0.0)      # 0 for compute-only dummy kernel

def S(n,k): return s0 + (s1 + s2*k)*n
def W(n,k): return (w1 + w2*k)*n
def eps_of(k): return A*math.exp(-sigma*k)

# Choose k from error, then n from memory, then shrink to meet time/energy
k_min = math.ceil((1.0/sigma)*math.log(max(A/EPS_MAX,1.0)))
k = max(1, int(k_min))

def n_max_for(k):
    cap = M_max/max(c_mem,1e-9) - s0
    den = (s1 + s2*k)
    return max(0, int(cap/den))

n = n_max_for(k)
if n <= 0:
    raise SystemExit("[select] memory guard left no room; relax EPS_MAX or raise M_MAX")

def predict(n,k):
    work = W(n,k)
    T_hat = c_time * work
    E_hat = c_energy * work + E0
    M_hat = c_mem * S(n,k)
    # Optional I/O path (off for dummy kernel)
    X = IO_FRAC * S(n,k)
    T_io = X/max(beta,1.0)
    T_pred = max(T_hat, T_io) if IO_FRAC > 0.0 else T_hat
    return T_pred, E_hat, M_hat

# Shrink n until all budgets hold
while n > 0:
    T_pred, E_pred, M_pred = predict(n,k)
    if (T_pred <= L_max) and (E_pred <= E_max or c_energy == 0.0) and (M_pred <= M_max):
        break
    n = int(n * 0.9)

if n <= 0:
    raise SystemExit("[select] no feasible (n,k); relax budgets or adjust model coefficients")

# Pre-certificate
T_pred, E_pred, M_pred = predict(n,k)
pre = {
  "selected": {"n": int(n), "k": int(k)},
  "budgets": {"L_max": L_max, "E_max": E_max, "M_max": M_max, "EPS_MAX": EPS_MAX, "TAU_STAR": TAU_STAR},
  "predicted": {"T": T_pred, "E": E_pred, "M": M_pred, "eps": eps_of(k)},
  "models": {"S":{"s0":s0,"s1":s1,"s2":s2}, "W":{"w1":w1,"w2":w2}, "error":{"A":A,"sigma":sigma}},
  "passport_ref": passport_path
}
os.makedirs(".tau_ledger/physics", exist_ok=True)
open(".tau_ledger/physics/pre_cert.json","w",encoding="utf-8").write(json.dumps(pre, indent=2))

# Debug for sanity
print(f"[select/debug] c_time={c_time} IO_FRAC={IO_FRAC} beta={beta}  W={W(n,k)}  S={S(n,k)}")
print(f"[select] chose n={n} k={k}  T^={T_pred:.6f} s  M^={M_pred/2**30:.3f} GiB  eps^={eps_of(k):.3e}")
