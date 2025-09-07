#!/usr/bin/env python3
import os, json, math, sys, time
def rd(x):
  return None if x is None else float(x)
passport=json.load(open(".tau_ledger/physics/passport.json","r",encoding="utf-8")) if os.path.exists(".tau_ledger/physics/passport.json") else {}
M_phys = rd(passport.get("gpu",{}).get("mem_total_bytes")) or rd(passport.get("cpu",{}).get("mem_total_bytes")) or 4.0e9
beta   = rd(passport.get("io",{}).get("beta_sustained_bytes_per_s")) or 2.0e9
c_time = rd(passport.get("coefficients",{}).get("c_time")) or 1e-9
c_energy = rd(passport.get("coefficients",{}).get("c_energy")) or 0.0
c_mem = rd(passport.get("coefficients",{}).get("c_mem")) or 1.0
E0 = rd(passport.get("coefficients",{}).get("E0")) or 0.0
# model coefficients (tune per kernel; defaults are sane placeholders)
s0=0.0; s1=8.0; s2=8.0
w1=3.0; w2=5.0
A=1.0; sigma=0.08
L_max=float(os.environ.get("L_MAX","2.0"))
E_max=float(os.environ.get("E_MAX","50.0"))
M_max=float(os.environ.get("M_MAX", str(M_phys*0.8)))
EPS_MAX=float(os.environ.get("EPS_MAX","1e-6"))
TAU_STAR=float(os.environ.get("TAU_STAR","12"))
def S(n,k): return s0 + s1*n + s2*k*n
def W(n,k): return w1*n + w2*k*n
def eps_of(k): return A*math.exp(-sigma*k)
# solve k from error bound
k_min = math.ceil((1.0/sigma)*math.log(max(A/EPS_MAX,1.0)))
# memory guard -> n_max for that k
def n_max_for(k):
  # s0 + (s1 + s2*k) n <= M_max/c_mem
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
  X = S(n,k)  # crude bytes moved proxy
  T_io = X/max(beta,1.0) + 0.0
  T_pred = max(T_hat, T_io)
  return T_pred, E_hat, M_hat
T_pred,E_pred,M_pred = predict(n,k)
# shrink n until within L/E/M budgets
while n>0:
  T_pred,E_pred,M_pred = predict(n,k)
  if T_pred<=L_max and (E_pred<=E_max or c_energy==0.0) and M_pred<=M_max: break
  n = int(n*0.9)
if n<=0:
  raise SystemExit("[select] no feasible (n,k) under budgets; relax budgets or adjust models")
pre={
  "selected": {"n": int(n), "k": int(k)},
  "budgets": {"L_max": L_max, "E_max": E_max, "M_max": M_max, "EPS_MAX": EPS_MAX, "TAU_STAR": TAU_STAR},
  "predicted": {"T": T_pred, "E": E_pred, "M": M_pred, "eps": eps_of(k)},
  "models": {"S": {"s0":s0,"s1":s1,"s2":s2}, "W":{"w1":w1,"w2":w2}, "error":{"A":A,"sigma":sigma}},
  "passport_ref": ".tau_ledger/physics/passport.json"
}
open(".tau_ledger/physics/pre_cert.json","w",encoding="utf-8").write(json.dumps(pre,indent=2))
print("[select] chose n=%d k=%d  T^=%.3f  M^=%.3f GiB  eps^=%.3e" % (n,k,T_pred,M_pred/2**30,pre["predicted"]["eps"]))
