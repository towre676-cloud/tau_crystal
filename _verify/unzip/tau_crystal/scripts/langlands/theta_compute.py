import sys, os, re
s=float(sys.argv[1]) if len(sys.argv)>1 else 1.0
t=float(sys.argv[2]) if len(sys.argv)>2 else 0.0
root=sys.argv[3] if len(sys.argv)>3 else ".tau_ledger"
floats=re.compile(rb"[0-9]+(?:\.[0-9]+)?")
total=0.0; count_vals=0; files=0
for dp,_,fs in os.walk(root):
  for fn in fs:
    if not fn.endswith(".json"): continue
    p=os.path.join(dp,fn)
    try: data=open(p,"rb").read()
    except: continue
    vals=[float(x) for x in floats.findall(data)]
    if not vals: continue
    m=max(vals) or 1.0
    for v in vals:
      z=min(1.0,max(1e-12, v/m))
      u=s*z + t
      if u<1e-12: u=1e-12
      if u>1.0: u=1.0
      total += u; count_vals += 1
    files += 1
mean = (total/count_vals) if count_vals else 0.0
print(f"{mean:.12f}\t{files}\t{count_vals}")
