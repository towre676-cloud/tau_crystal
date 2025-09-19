import io, json, sys, hashlib, os
seed = sys.argv[1] if len(sys.argv)>1 else "0"
h = hashlib.sha256(seed.encode()).hexdigest()
tau = [int(h[i:i+2],16)/255.0 for i in range(0,64,2)]
def T(p):
    return sum(tau[k % 32] for k in range(p)) / p
hecke = {"T_2": T(2), "T_3": T(3), "T_5": T(5), "T_7": T(7), "T_11": T(11)}
obj = {"seed": seed, "tau": tau, "hecke": hecke}
os.makedirs(".tau_ledger/automorphic", exist_ok=True)
path = f".tau_ledger/automorphic/hecke_{seed}.json"
io.open(path, "w", encoding="utf-8").write(json.dumps(obj, ensure_ascii=False, indent=2)+"\n")
print(path)
