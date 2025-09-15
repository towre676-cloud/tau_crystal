import io,json,math,os,sys
hecke_path=sys.argv[1] if len(sys.argv)>1 else None
out=".tau_ledger/experimental/symsquare_zeros.json"
os.makedirs(os.path.dirname(out),exist_ok=True)
if not hecke_path:
    json.dump({"sym2_zeros":[],"truncation":{"primes_used":[],"error_bound":None}},io.open(out,"w",encoding="utf-8"),indent=2)
    print(out); sys.exit(0)
H=json.load(io.open(hecke_path,"r",encoding="utf-8"))
T=H.get("hecke",{})
primes=[int(k.split("_")[1]) for k in T if k.startswith("T_")]
primes.sort()
alpha={p:float(T[f"T_{p}"]) for p in primes}
grid=[0.5,1.0,1.5,2.0]
zeros=[]
for s in grid:
    L=1.0
    for p in primes:
        denom=1.0-alpha[p]*alpha[p]*(p**(-s))
        if abs(denom)<1e-12: denom=1e-12
        L*=1.0/denom
    if L*L<1e-6: zeros.append({"s":s,"L_sym2":L})
trunc_err=sum(alpha[p]*alpha[p]*(p**(-2.0)) for p in primes[-3:])  # tail proxy
json.dump({"sym2_zeros":zeros,"truncation":{"primes_used":primes,"error_bound":trunc_err}},io.open(out,"w",encoding="utf-8"),indent=2)
print(out)
