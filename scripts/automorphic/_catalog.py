import io,json,datetime as dt
M=".tau_ledger/manifest.json"; D="docs/automorphic/catalog.md"
man=json.load(io.open(M,"r",encoding="utf-8")) if io.open(M,"r",encoding="utf-8") else {"automorphic":[]}
rows=[]
for m in man.get("automorphic",[]):
  seed=str(m.get("seed"))
  n=len(m.get("tau",[])) if isinstance(m.get("tau"),list) else 0
  rows.append((seed,n))
rows.sort(key=lambda x:x[0])
out=["# Automorphic Catalog","",f"_updated: {dt.datetime.utcnow().isoformat()}Z_","", "| seed | τ-length |", "|---:|---:|"]
out+= [f"| {s} | {n} |" for s,n in rows]
io.open(D,"w",encoding="utf-8").write("\n".join(out)+"\n")
