import io,json,math,os,sys,random
import numpy as np
csv_path=".tau_ledger/seq/tau.csv"; out=".tau_ledger/experimental/bootstrap_mu.json"
os.makedirs(os.path.dirname(out),exist_ok=True)
try:
  lines=io.open(csv_path,"r",encoding="utf-8").read().strip().splitlines()
except FileNotFoundError:
  json.dump({"bootstrap_mu":{}},io.open(out,"w",encoding="utf-8")); print(out); sys.exit(0)
vals=[float(l.split(",")[1]) for i,l in enumerate(lines) if i>0 and len(l.split(","))>=2]
if len(vals)<10:
  json.dump({"bootstrap_mu":{}},io.open(out,"w",encoding="utf-8")); print(out); sys.exit(0)
primes=[2,3,5,7,11,13,17,19]; B=2000; seed=42; rng=random.Random(seed)
mu_slopes=[]
for _ in range(B):
  boot=np.random.choice(vals,size=len(vals),replace=True)
  slopes=[]
  for p in primes:
    for n in range(1,9):
      mod=int(p**n); s=0.0
      for k,v in enumerate(boot,start=1):
        ang=2*math.pi*((k % mod)/mod); s+=math.cos(ang)*v
      slope=(-99 if s==0 else math.log(abs(s))/n); slopes.append(slope)
  mu_slopes.append(float(np.mean(slopes)))
jack=np.mean([np.mean([s for i,s in enumerate(mu_slopes) if i!=j]) for j in range(len(mu_slopes))])
bias_corr=2*np.mean(mu_slopes)-jack
ci_lo,ci_hi=np.percentile(mu_slopes,[2.5,97.5])
obj={"mu_slope":float(np.mean(mu_slopes)),"bias_corrected":float(bias_corr),"ci_lower":float(ci_lo),"ci_upper":float(ci_hi),"B":B,"seed":seed}
json.dump({"bootstrap_mu":obj},io.open(out,"w",encoding="utf-8"),indent=2); print(out)
