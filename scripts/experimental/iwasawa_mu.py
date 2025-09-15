import io,json,math,sys
csv_path=".tau_ledger/seq/tau.csv"; out=".tau_ledger/iwasawa/mu_sampling.json"
import os; os.makedirs(".tau_ledger/iwasawa",exist_ok=True)
try: lines=io.open(csv_path,"r",encoding="utf-8").read().strip().splitlines()
except FileNotFoundError: io.open(out,"w",encoding="utf-8").write("{\"mu_samples\":[]}\n"); print(out); sys.exit(0)
vals=[]
for i,l in enumerate(lines):
  if i==0: continue
  parts=l.split(",")
  if len(parts)>=2:
    try: vals.append(float(parts[1]))
    except: pass
primes=[2,3,5,7,11,13,17,19]
samples=[]
for p in primes:
  for n in range(1,9):
    s=0.0
    mod=int(p**n)
    for k,v in enumerate(vals, start=1):
      ang=2*math.pi*((k % mod)/mod)
      s+=math.cos(ang)*v
    slope = (-99.0 if s==0 else math.log(abs(s))/n)
    samples.append({"p":p,"n":n,"chi_sum":s,"mu_slope":slope})
io.open(out,"w",encoding="utf-8").write(json.dumps({"mu_samples":samples},ensure_ascii=False,indent=2)+"\n")
print(out)
