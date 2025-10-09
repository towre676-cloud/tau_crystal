import sys,json,io,csv,math
rec,pts,ht = sys.argv[1], sys.argv[2], sys.argv[3]
with io.open(rec,"r",encoding="utf-8") as f: R=json.load(f)
X=[]
if os:=pts:
  with io.open(os,"r",encoding="utf-8") as f:
    for i,row in enumerate(csv.reader(f)):
      if i==0 or (row and row[0].startswith("#")): continue
      X.append({"x":row[0],"y":row[1] if len(row)>1 else ""})
H=[]
if hs:=ht:
  with io.open(hs,"r",encoding="utf-8") as f:
    for i,row in enumerate(csv.reader(f)):
      if i==0 or (row and row[0].startswith("#")): continue
      try: H.append(float(row[2]))
      except: pass
reg = None
if H:
  # placeholder: sum of diagonal entries if you feed diagonals; replace with det of height matrix later
  reg = sum(H)
R.setdefault("points",{}).update({"x_coords":[p["x"] for p in X]})
if reg is not None: R.setdefault("curve",{}).update({"regulator_estimate":reg})
with io.open(rec,"w",encoding="utf-8") as f: f.write(json.dumps(R,ensure_ascii=False,separators=(",",":"))+"\n")
