#!/usr/bin/env python3
import math,json,argparse,sys
def one_loop_demo(b=1.0,mu0=0.1,ell=0.73,n=2.0,c=1.0):
  if not (b>0 and mu0>0): raise ValueError("require b>0, mu0>0")
  if not (ell<1.0/(b*mu0)): raise ValueError("ell must be below pole 1/(b*mu0)")
  mu=mu0/(1.0-b*mu0*ell)
  I_res=(1.0/mu)+b*ell-(1.0/mu0)
  S=mu-mu0
  F=-(n*c)/(2.0*b)*math.log(mu); F0=-(n*c)/(2.0*b)*math.log(mu0); dF=F-F0
  r=math.log(mu/mu0); logA=(n*c)/(2.0*b)*r
  Ls=math.sqrt(n*c/(2.0*b))*r
  fisher_res=logA - math.sqrt(n*c/(2.0*b))*Ls
  amp_vs_dF_res=logA + dF
  N=(1.0/(6.0*b))*math.log(1.0/(1.0-b*mu0*ell))
  ell_k=lambda k:(1.0/(b*mu0))*(1.0-math.exp(-3.0*b*k))
  return {"params":{"b":b,"mu0":mu0,"ell":ell,"n":n,"c":c},
          "mu":mu,"invariant_residual":I_res,"entropy":S,"F":F,"F_delta":dF,
          "logA_rel":logA,"L_signed":Ls,"fisher_relation_residual":fisher_res,
          "amplitude_vs_dF_residual":amp_vs_dF_res,"scheduler_N":N,
          "wall_times":{int(k):ell_k(k) for k in range(1,6)}}
def two_loop_demo(b=1.0,b1=0.2,mu0=0.1,ell=0.73,n=2.0,c=1.0,steps=8):
  if not (b>0 and mu0>0): raise ValueError("require b>0, mu0>0")
  def rhs(x): return -1.0/(b*x)+(b1/(b*b))*math.log((b+b1*x)/x)
  def drhs(x): return 1.0/(b*x*x)+(b1/(b*b))*(b1/(b+b1*x)-1.0/x)
  target=rhs(mu0)+ell; x=mu0
  for _ in range(steps): x-= (rhs(x)-target)/drhs(x)
  mu2=x; resid=rhs(mu2)-target; alpha=b1/b
  logA2=(n*c)/(2.0*b)*(math.log(mu2)-math.log(1.0+alpha*mu2)-math.log(mu0)+math.log(1.0+alpha*mu0))
  return {"params":{"b":b,"b1":b1,"mu0":mu0,"ell":ell,"n":n,"c":c},
          "mu":mu2,"integral_residual":resid,"logA2":logA2,"newton_steps":steps}
def _f2(x): return float(f"{x:.16g}")
def main():
  ap=argparse.ArgumentParser(add_help=False)
  for k,d in (("b",1.0),("b1",0.2),("mu0",0.1),("ell",0.73),("n",2.0),("c",1.0)):
    ap.add_argument("--"+k,type=float,default=d)
  ap.add_argument("--json",action="store_true"); ap.add_argument("--out",type=str,default=""); ap.add_argument("--help",action="store_true")
  a=ap.parse_args()
  if a.help:
    print("usage: python scripts/rg/affine_leaf.py [--json] [--out file] [--b --b1 --mu0 --ell --n --c]"); sys.exit(0)
  one=one_loop_demo(a.b,a.mu0,a.ell,a.n,a.c); two=two_loop_demo(a.b,a.b1,a.mu0,a.ell,a.n,a.c)
  if a.json:
    rec={"schema":"taucrystal/rg_affine_leaf/v1","params":{k:_f2(v) for k,v in one["params"].items()},"params_b1":_f2(a.b1),
         "one_loop":{k:(_f2(v) if isinstance(v,(float,int)) else {kk:_f2(vv) for kk,vv in v.items()}) for k,v in one.items() if k!="params"},
         "two_loop":{k:(_f2(v) if isinstance(v,(float,int)) else v) for k,v in two.items() if k!="params"} }
    js=json.dumps(rec,sort_keys=True,separators=(",",":"))
    if a.out: open(a.out,"w",encoding="utf-8").write(js)
    else: sys.stdout.write(js)
    return
  pr=lambda x:f"{x:.3e}"
  print("== Affine RG leaf: one-line invariant, certified numerics ==")
  print("\\n[one-loop] params:",one["params"])
  print("mu =",pr(one["mu"]))
  print("invariant residual I(mu,ell) =",pr(one["invariant_residual"]))
  print("entropy S = mu - mu0         =",pr(one["entropy"]))
  print("CS - Fisher residual         =",pr(one["fisher_relation_residual"]))
  print("logA_rel, L_signed           =",pr(one["logA_rel"]),pr(one["L_signed"]))
  print("scheduler N(ell)             =",pr(one["scheduler_N"]))
  print("half-step walls ell_k (k=1..5):")
  for k,v in one["wall_times"].items(): print(f"  k={k:2d}: ell_k = {v:.10f}")
  print("\\n[two-loop] params:",two["params"])
  print("mu(ell) =",pr(two["mu"]))
  print("integral residual            =",pr(two["integral_residual"]))
  print("two-loop log(A/A0)           =",pr(two["logA2"]))
if __name__=="__main__": main()
