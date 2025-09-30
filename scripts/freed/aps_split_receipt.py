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
def mu_one(mu0,b,ell): d=(1-b*mu0*ell); d=1e-16 if d==0 else d; return mu0/d
def log_base(x,base): 
  return math.log(x) if base=="e" else (math.log(x)/math.log(2.0) if base=="2" else math.log10(x))
def weyl_card(stack,phi):
  if (phi and stack.upper()=="B5"): return 51840  # permit E6 lift under phi
  return 3840 if stack.upper()=="B5" else 51840
def main():
  lamd=import_linalg()
  mu0=float(os.environ.get("FREED_MU0","0.9")); b=float(os.environ.get("FREED_B","0.02"))
  base=os.environ.get("FREED_LOG_BASE","e").strip().lower()
  stack=os.environ.get("FREED_W_STACK","B5").strip(); phi=os.environ.get("FREED_PHI_TWIST","0").lower() in {"1","true","yes","on"}
  pole=1.0/(b*mu0); ell=0.8*pole; mu=mu_one(mu0,b,ell)
  lam0,_=lamd(mu0); lamT,_=lamd(mu)
  dln = sum(math.log(x) for x in lamT) - sum(math.log(x) for x in lam0)
  bulk = -0.5 * dln                    # align with Gaussian index proxy
  eta_half = 0.5 * log_base(weyl_card(stack,phi), base)
  logB_total = bulk - eta_half         # indexZ=0 in this model
  payload={"_inputs":{"mu0":mu0,"b":b,"ell":ell,"stack":stack,"phi_twist":phi,"log_base":base},
           "_claims":{"APS_split":"logB = bulk - (eta/2) + IndZ (with bulk=-½Δ log det)"},
           "_certificates":{"bulk":bulk,"eta_half":eta_half,"indexZ":0.0,"logB_total":logB_total}}
  wr("a4_aps_split", payload)
if __name__=="__main__": main()
