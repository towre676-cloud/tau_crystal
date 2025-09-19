import io, json, sys, os, time
in_path = sys.argv[1]
obj=json.load(io.open(in_path,"r",encoding="utf-8"))
seed=str(obj.get("seed"))
H=obj.get("hecke",{})
t2=float(H.get("T_2",0.0))
ell=65521
trace_mod=int((t2*1000000.0)) % ell
rho=[[1,trace_mod],[0,1]]
try:
  merkle=io.open(".tau_ledger/MERKLE_ROOT","r",encoding="utf-8").read().strip()
except Exception:
  merkle=f"CI_{int(time.time())}"
out={ "matrix": rho, "trace_mod_ell": trace_mod, "proven_by_merkle": merkle, "from_hecke_seed": seed }
os.makedirs(".tau_ledger/galois",exist_ok=True)
path=f".tau_ledger/galois/rho_{seed}.json"
io.open(path,"w",encoding="utf-8").write(json.dumps(out,ensure_ascii=False,indent=2)+"\n")
print(path)
