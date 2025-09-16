import sys, json, math
def f2(x): return float(f"{x:.16g}")
def run(b=1.0, mu0=0.1, ell=0.73, n=2.0, c=1.0, b1=0.0, kmax=6):
  b=float(b); mu0=float(mu0); ell=float(ell); n=float(n); c=float(c); b1=float(b1); kmax=int(kmax)
  # one-loop closed form
  mu = mu0 / (1.0 - b*mu0*ell)
  inv_res = (1.0/mu + b*ell - 1.0/mu0)
  S = mu - mu0
  F = -(n*c)/(2.0*b)*math.log(mu)
  F0 = -(n*c)/(2.0*b)*math.log(mu0)
  dF = F - F0
  logA = (n*c)/(2.0*b)*math.log(mu/mu0)
  Lgeo = math.sqrt((n*c)/(2.0*b))*abs(math.log(mu/mu0))
  # Signed Fisher relation: logA = sqrt(nc/2b) * signed(Lgeo)
  sgn = 1.0 if mu>=mu0 else -1.0
  fisher_res = logA - sgn*Lgeo*math.sqrt((n*c)/(2.0*b))
  amp_vs_dF_res = logA + dF
  # Hex scheduler
  N_ell = (1.0/(6.0*b))*math.log(1.0/(1.0 - b*mu0*ell))
  ells = [ (1.0/(b*mu0))*(1.0 - math.exp(-3.0*b*k)) for k in range(kmax+1) ]
  two = {}
  if abs(b1)>0.0:
    def rhs(x): return -1.0/(b*x) + (b1/(b*b))*math.log((b + b1*x)/x)
    def drhs(x): return 1.0/(b*x*x) + (b1/(b*b))*(b1/(b + b1*x) - 1.0/x)
    target = rhs(mu0) + ell
    x = mu0
    for _ in range(12):
      fx = rhs(x) - target
      d = drhs(x)
      x -= fx/d
    two = {"mu": f2(x), "residual": f2(rhs(x)-target)}
  out = {
    "schema":"taucrystal/rg_affine_leaf/v1",
    "params":{"b":f2(b),"mu0":f2(mu0),"ell":f2(ell),"n":f2(n),"c":f2(c),"b1":f2(b1),"kmax":kmax},
    "one_loop":{
      "mu":f2(mu),
      "invariant_residual":f2(inv_res),
      "entropy":f2(S),
      "F_delta":f2(dF),
      "logA":f2(logA),
      "L_geo":f2(Lgeo),
      "fisher_relation_residual":f2(fisher_res),
      "amplitude_vs_dF_residual":f2(amp_vs_dF_res)
    },
    "scheduler":{"N_ell":f2(N_ell),"ell_steps":[f2(e) for e in ells]},
    "two_loop": two
  }
  sys.stdout.write(json.dumps(out, sort_keys=True, separators=(",",":")))
if __name__=="__main__":
  args = sys.argv[1:]
  vals = [float(a) for a in args] if args else []
  while len(vals)<7: vals.append([1.0,0.1,0.73,2.0,1.0,0.0,6][len(vals)])
  sys.stdout.write(run(*vals))
