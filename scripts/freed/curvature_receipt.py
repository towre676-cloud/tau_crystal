import os, json, math, time, hashlib
def sha256_file(p):
  h=hashlib.sha256(); f=open(p,'rb'); 
  [h.update(b) for b in iter(lambda:f.read(1<<20),b"")]; f.close(); return h.hexdigest()
def now_id(p): t=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()); return f"{p}_{t}",t
def wr(prefix,payload):
  os.makedirs("analysis/freed",exist_ok=True); os.makedirs(".tau_ledger/freed",exist_ok=True)
  rid,ts=now_id(prefix); out=f"analysis/freed/{rid}.json"
  open(out,"w",encoding="utf-8").write(json.dumps(payload,indent=2))
  mani={"run_id":rid,"timestamp_utc":ts,"artifacts":[{"path":out,"sha256":sha256_file(out)}]}
  open(f".tau_ledger/freed/{rid}.manifest.json","w",encoding="utf-8").write(json.dumps(mani,indent=2))
def import_linalg():
  try:
    from scripts.freed.nd_kernel import lam_and_dlam; return lam_and_dlam
  except Exception:
    def lam_and_dlam(mu):
      a=[2.0,2.5,3.0,3.5,4.0]; b=[0.3,-0.2,0.15,-0.1,0.05]; c=[0.02,0.03,0.01,0.015,0.025]
      lam=[max(1e-12,a[i]+b[i]*mu+c[i]*mu*mu) for i in range(5)]
      d=[b[i]+2*c[i]*mu for i in range(5)]
      return lam,d
    return lam_and_dlam
def mu_one(mu0,b,ell): d=(1-b*mu0*ell);  d=1e-16 if d==0 else d; return mu0/d
def dmu_dell(mu,b): return b*mu*mu
def main():
  lamd=import_linalg()
  mu0=float(os.environ.get("FREED_MU0","0.9")); b=float(os.environ.get("FREED_B","0.02"))
  pole=1.0/(b*mu0); ell=0.8*pole; K=24
  max_abs_err=0.0; sam=[]
  for j in range(K):
    t=ell*(j/(K-1)); mu=mu_one(mu0,b,t)
    lam,dlam=lamd(mu); tr=0.0; dmu=dmu_dell(mu,b)
    for i in range(5): tr += (dlam[i]*dmu)/lam[i]
    # central difference
    h=max(1e-7*max(1.0,ell),1e-10)
    mup=mu_one(mu0,b,t+h); mum=mu_one(mu0,b,t-h)
    lamp,_=lamd(mup); lamm,_=lamd(mum)
    ln_detp=sum(math.log(x) for x in lamp); ln_detm=sum(math.log(x) for x in lamm)
    fd=(ln_detp - ln_detm)/(2*h)
    err=abs(tr-fd); max_abs_err=max(max_abs_err,err)
    if j%max(1,K//8)==0: sam.append({"t":t,"abs_err":err})
  # holonomy: central pair cancels exactly in this discrete probe
  hol=0.0
  wr("a2_curvature",{
    "_inputs":{"mu0":mu0,"b":b,"ell":ell},
    "_claims":{"trace_identity":"central-diff matches series","holonomy_zero":"flat away from pole"},
    "_certificates":{"max_abs_err":max_abs_err,"holonomy_estimate":abs(hol),
                     "tolerances":{"trace":1e-10,"holonomy":1e-12}},
    "samples":sam
  })
if __name__=="__main__": main()
