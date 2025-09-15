import io,json,math,sys
in_path=sys.argv[1] if len(sys.argv)>1 else None
out=".tau_ledger/experimental/symsquare_zeros.json"
import os; os.makedirs(".tau_ledger/experimental",exist_ok=True)
if not in_path: io.open(out,"w",encoding="utf-8").write("{\"sym2_zeros\":[]}\n"); print(out); sys.exit(0)
H=json.load(io.open(in_path,"r",encoding="utf-8"))
T=H.get("hecke",{})
a2=float(T.get("T_2",0.0)); a3=float(T.get("T_3",0.0)); a5=float(T.get("T_5",0.0))
grid=[0.5,1.0,1.5,2.0]
zeros=[]
def Lp(a,p,s): return 1.0/(1.0 - (a*a)*(p**(-s))) if abs(1.0 - (a*a)*(p**(-s)))>1e-12 else 1e12
for s in grid:
  L = Lp(a2,2,s)*Lp(a3,3,s)*Lp(a5,5,s)
  if L*L < 1e-6: zeros.append({"s":s,"L_sym2":L})
io.open(out,"w",encoding="utf-8").write(json.dumps({"sym2_zeros":zeros},ensure_ascii=False,indent=2)+"\n")
print(out)
