import sys, os, re, math, datetime
A = sys.argv[1] if len(sys.argv)>1 else ".tau_ledger"
B = sys.argv[2] if len(sys.argv)>2 else ".tau_ledger/demo"
floats = re.compile(rb"[0-9]+(?:\.[0-9]+)?")
def hecke_mean(root, n):
    total = 0.0; count = 0
    for dp,_,fs in os.walk(root):
        for fn in fs:
            if not fn.endswith(".json"): continue
            p = os.path.join(dp,fn)
            try: data = open(p,"rb").read()
            except: continue
            vals = [float(x) for x in floats.findall(data)]
            if not vals: continue
            m = max(vals) or 1.0
            for v in vals:
                x = min(1.0, max(1e-12, v/m))
                s = 0.0
                for k in range(1, n+1): s += x**(k/float(n))
                total += s/n; count += 1
    return (total/count) if count else 0.0
def theta_mean(root, s, t):
    total = 0.0; count = 0
    for dp,_,fs in os.walk(root):
        for fn in fs:
            if not fn.endswith(".json"): continue
            p = os.path.join(dp,fn)
            try: data = open(p,"rb").read()
            except: continue
            vals = [float(x) for x in floats.findall(data)]
            if not vals: continue
            m = max(vals) or 1.0
            for v in vals:
                z = min(1.0, max(1e-12, v/m))
                u = s*z + t
                if u < 1e-12: u = 1e-12
                if u > 1.0: u = 1.0
                total += u; count += 1
    return (total/count) if count else 0.0
ns = [3,4,5,6,7,8,9,10]
ss = [0.70,0.75,0.80,0.85,0.90,0.95,1.00]
ts = [0.00,0.01,0.02,0.03,0.04]
ts_now = datetime.datetime.utcnow().strftime("%Y%m%dT%H%M%SZ")
out = os.path.join("analysis", f"modularity_scan_{ts_now}.tsv")
os.makedirs("analysis", exist_ok=True)
with open(out,"w",encoding="utf-8") as fh:
    fh.write("n\ts\tt\tDelta\ta\tb\n")
    a_cache = {}
    for n in ns:
        a = a_cache.get(n);
        if a is None:
            a = hecke_mean(A, n); a_cache[n] = a
        for s in ss:
            for t in ts:
                b = theta_mean(B, s, t)
                d = abs(a-b)
                fh.write(f"{n}\t{s:.2f}\t{t:.2f}\t{d:.12f}\t{a:.12f}\t{b:.12f}\n")
print(out)
