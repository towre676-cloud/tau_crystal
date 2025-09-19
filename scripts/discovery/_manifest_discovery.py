import io,json,os
M=".tau_ledger/manifest.json"
man=json.load(io.open(M,"r",encoding="utf-8")) if os.path.exists(M) else {}
man["discovery_primary"]={".tau_ledger/discovery/double_zero.json":"BSD @ Re=1/2 AND Sym^2 outside strip"}
io.open(M,"w",encoding="utf-8").write(json.dumps(man,ensure_ascii=False,indent=2)+"\\n")
