import sys,io,csv,json
rec,locals_csv,out = sys.argv[1], sys.argv[2], sys.argv[3]
with io.open(rec,"r",encoding="utf-8") as f: R=json.load(f)
disc_sign = (R.get("curve",{}).get("discriminant_sign") or R.get("discriminant_sign"))
w_inf = None
if isinstance(disc_sign,str): disc_sign = disc_sign.strip()
if disc_sign in ("-1","-","neg","negative"): w_inf = -1
elif disc_sign in ("+1","+","pos","positive"): w_inf = +1
else: w_inf = None
w_finite = 1
with io.open(locals_csv,"r",encoding="utf-8") as f:
    rd=csv.reader(f);
    for i,row in enumerate(rd):
        if i==0 or not row or row[0].startswith("#"): continue
        s = row[1].strip() if len(row)>1 else ""
        if s in ("-1","-"): w_finite *= -1
        elif s in ("+1","+"): w_finite *= +1
        else: pass
res = {"archimedean": w_inf, "finite_product": w_finite, "global": (w_inf*w_finite if (w_inf is not None) else None)}
with io.open(out,"w",encoding="utf-8") as f: f.write(json.dumps(res,separators=(",",":"))+"\n")
