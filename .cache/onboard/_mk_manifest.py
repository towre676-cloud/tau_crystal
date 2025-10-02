import sys,json
src,dst=sys.argv[1],sys.argv[2]
res=json.load(open(src,"rb"))
doc={"manifest_version":1,"producer":"demo","commit":res.get("commit","unknown"),"timestamp":res.get("timestamp_utc","unknown"),"tau_pulse":res.get("tau_pulse",0)}
json.dump(doc,open(dst,"w"),indent=2)
