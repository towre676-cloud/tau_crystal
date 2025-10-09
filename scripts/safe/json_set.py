import sys,io,json
p,key,val=sys.argv[1],sys.argv[2],sys.argv[3]
with io.open(p,"r",encoding="utf-8") as f: d=json.load(f)
cur=d; ks=key.split(".")
for k in ks[:-1]:
    if k not in cur or not isinstance(cur[k],dict): cur[k]={}
    cur=cur[k]
cur[ks[-1]]=val
with io.open(p,"w",encoding="utf-8") as f: f.write(json.dumps(d,separators=(",",":"))+"\n")
