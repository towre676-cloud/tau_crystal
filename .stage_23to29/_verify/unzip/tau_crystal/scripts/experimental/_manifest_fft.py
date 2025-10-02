import io,json
M=".tau_ledger/manifest.json"
man=json.load(io.open(M,"r",encoding="utf-8")) if __import__("os").path.exists(M) else {}
man["fft_bootstrap"]={
  "fft_bsd":".tau_ledger/experimental/fft_bsd.json",
  "bootstrap_mu":".tau_ledger/experimental/bootstrap_mu.json"
}
io.open(M,"w",encoding="utf-8").write(json.dumps(man,ensure_ascii=False,indent=2)+"\n")
