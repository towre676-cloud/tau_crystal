import io,json,os
M=".tau_ledger/manifest.json"
man=json.load(io.open(M,"r",encoding="utf-8"))
man["experimental_v2"]={
  "bsd_rank1":".tau_ledger/experimental/bsd_rank1.json",
  "sym2_dynamic":".tau_ledger/experimental/symsquare_zeros.json"
}
io.open(M,"w",encoding="utf-8").write(json.dumps(man,ensure_ascii=False,indent=2)+"\n")
