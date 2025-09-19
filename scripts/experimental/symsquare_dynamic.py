import io,json,math,os,sys
hp=sys.argv[1] if len(sys.argv)>1 else None
out=".tau_ledger/experimental/symsquare_zeros.json"
os.makedirs(os.path.dirname(out),exist_ok=True)
def write(obj): io.open(out,"w",encoding="utf-8").write(json.dumps(obj,ensure_ascii=False,indent=2)+"\\n")
if not hp:
  write({"data":{"sym2_zeros":[],"truncation":{"primes_used":[],"error_bound":None}}}); print(out); sys.exit(0)
H=json.load(io.open(hp,"r",encoding="utf-8")); T=H.get("hecke",{})
primes=sorted(int(k.split("_")[1]) for k in T if k.startswith("T_"))
alpha={p:float(T[f"T_{p}"]) for p in primes}
grid=[0.5,1.0,1.5,2.0]; zeros=[]
for s in grid:
  L=1.0
  for p in primes:
    den=1.0 - alpha[p]*alpha[p]*(p**(-s)); den = den if abs(den)>1e-12 else 1e-12
    L*=1.0/den
  if L*L<1e-6: zeros.append({"s":s,"L_sym2":L})
tail=primes[-3:] if len(primes)>=3 else primes
terr=sum(alpha[p]*alpha[p]*(p**(-2.0)) for p in tail) if tail else None
write({"data":{"sym2_zeros":zeros,"truncation":{"primes_used":primes,"error_bound":terr}}})
print(out)
