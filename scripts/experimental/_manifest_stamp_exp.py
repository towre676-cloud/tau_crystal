import io,json,os
M=".tau_ledger/manifest.json"
os.makedirs(".tau_ledger",exist_ok=True)
try: man=json.load(io.open(M,"r",encoding="utf-8"))
except Exception: man={"automorphic":[]}
man["experimental_primary"]={
  "bsd_rank1": ".tau_ledger/experimental/bsd_rank1.json",
  "sym2_zeros": ".tau_ledger/experimental/symsquare_zeros.json",
  "iwasawa_mu": ".tau_ledger/iwasawa/mu_sampling.json"}
io.open(M,"w",encoding="utf-8").write(json.dumps(man,ensure_ascii=False,indent=2)+"\n")
