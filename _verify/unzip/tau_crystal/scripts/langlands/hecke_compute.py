import sys, os, re, math
n=int(sys.argv[1]) if len(sys.argv)>1 else 3
root=sys.argv[2] if len(sys.argv)>2 else ".tau_ledger"
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
    seq=[min(1.0,max(1e-12,v/m)) for v in vals]
    for x in seq:
      s=0.0
      for k in range(1,n+1): s+= x**(k/float(n))
      total += s/n; count_vals += 1
    files += 1
mean = (total/count_vals) if count_vals else 0.0
print(f"{mean:.12f}\t{files}\t{count_vals}")
