import json,datetime,os,sys
paths=[".tau_ledger/experimental/fft_bsd.json",".tau_ledger/experimental/bootstrap_mu.json"]
now=datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00","Z")
for p in paths:
  if not os.path.isfile(p): continue
  with open(p,"r",encoding="utf-8") as f: obj=json.load(f)
  if isinstance(obj,dict):
    prov=obj.get("provenance",{})
    prov["timestamp"]=now
    obj["provenance"]=prov
    txt=json.dumps(obj,sort_keys=True,separators=(",",":"))+"\\n"
    tmp=p+".tmp"; open(tmp,"w",encoding="utf-8",newline="\\n").write(txt); os.replace(tmp,p)
