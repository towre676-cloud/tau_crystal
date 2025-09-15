import io,json,math,sys
csv_path=".tau_ledger/seq/tau.csv"; out=".tau_ledger/experimental/bsd_rank1.json"
try: lines=io.open(csv_path,"r",encoding="utf-8").read().strip().splitlines()
except FileNotFoundError: io.open(out,"w",encoding="utf-8").write("{\"rank1_candidates\":[]}\n"); print(out); sys.exit(0)
ys=[]
for i,l in enumerate(lines):
  if i==0: continue
  parts=l.split(",")
  if len(parts)>=2:
    try: ys.append(float(parts[1]))
    except: pass
n=len(ys)
if n<5: io.open(out,"w",encoding="utf-8").write("{\"rank1_candidates\":[]}\n"); print(out); sys.exit(0)
m=n//2
mean=(ys[m-1]+ys[m])/2 if m>0 and m<n else 0.0
d1=(ys[m]-ys[m-2])/2 if m>=2 else 0.0
d2=(ys[m+1]-2*ys[m-1]+ys[m-3]) if m>=3 and m+1<n else 0.0
flag = 1 if (mean*mean<1e-8 and d1*d1>1e-8 and d2*d2<1e-8) else 0
obj={"rank1_candidates":[{"mean":mean,"d1":d1,"d2":d2,"rank1_flag":flag}]}
import os; os.makedirs(".tau_ledger/experimental",exist_ok=True)
io.open(out,"w",encoding="utf-8").write(json.dumps(obj,ensure_ascii=False,indent=2)+"\n")
print(out)
