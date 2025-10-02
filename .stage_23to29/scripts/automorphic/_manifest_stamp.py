import io,json,os
M=".tau_ledger/manifest.json"
os.makedirs(".tau_ledger", exist_ok=True)
try:
    man=json.load(io.open(M,"r",encoding="utf-8"))
except Exception:
    man={"automorphic":[]}
man["langlands_full"]={
  "critical_zeros": ".tau_ledger/automorphic/critical_zeros.json",
  "hecke_spectrum": ".tau_ledger/automorphic/hecke_*.json",
  "galois_rho": ".tau_ledger/galois/rho_*.json"
}
io.open(M,"w",encoding="utf-8").write(json.dumps(man,ensure_ascii=False,indent=2)+"\n")
