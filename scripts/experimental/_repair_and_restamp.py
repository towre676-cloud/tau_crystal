import sys,os,json,datetime,tempfile
def fix(p:str):
  if not os.path.isfile(p):
    print("[skip]",p,"missing"); return
  s=open(p,"r",encoding="utf-8",errors="replace").read()
  # parse only the first complete JSON object, ignoring concatenated tails
  start=s.find("{");
  if start<0: print("[err]",p,"no object start"); return
  dec=json.JSONDecoder();
  obj, end = dec.raw_decode(s[start:])
  if not isinstance(obj,dict):
    print("[err]",p,"top-level not object"); return
  # RFC3339Z timestamp
  now=datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00","Z")
  prov=obj.get("provenance",{})
  prov["timestamp"]=now
  obj["provenance"]=prov
  txt=json.dumps(obj,sort_keys=True,separators=(",",":"))+"\\n"
  tmp=p+".tmp"; open(tmp,"w",encoding="utf-8",newline="\\n").write(txt); os.replace(tmp,p)
  print("[fixed]",p,"len=",len(txt))
for path in sys.argv[1:]: fix(path)
