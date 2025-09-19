import io,json,math,sys
in_path=sys.argv[1] if len(sys.argv)>1 else None
out=".tau_ledger/experimental/symsquare_zeros.json"
import os; os.makedirs(".tau_ledger/experimental",exist_ok=True)
if not in_path: io.open(out,"w",encoding="utf-8").write("{\"sym2_zeros\":[]}\\n"); print(out); sys.exit(0)
H=json.load(io.open(in_path,"r",encoding="utf-8"))
T=H.get("hecke",{})
primes=[2,3,5,7,11,13]
alphas={p:float(T.get(f"T_{p}",0.0)) for p in primes}
grid=[0.5,1.0,1.5,2.0]
zeros=[]
def Lp(a,p,s): den=(1.0 - (a*a)*(p**(-s))); return (1.0/den) if abs(den)>1e-12 else 1e12
for s in grid:
  L=1.0
  for p,a in alphas.items(): L*=Lp(a,p,s)
  if L*L<1e-6: zeros.append({"s":s,"L_sym2":L,"primes":sorted(list(alphas.keys()))})
io.open(out,"w",encoding="utf-8").write(json.dumps({"sym2_zeros":zeros},ensure_ascii=False,indent=2)+"\\n")
print(out)
