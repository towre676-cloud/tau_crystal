import sys, json, statistics
from collections import defaultdict
src, out = sys.argv[1], sys.argv[2]
rows = []
with open(src, "r", encoding="utf-8") as f:
    for line in f:
        line=line.strip()
        if not line: continue
        try: obj=json.loads(line)
        except json.JSONDecodeError: continue
        rows.append(obj)
by_key = defaultdict(lambda: {"cold":[],"warm":[], "os":None, "runner":None})
for r in rows:
    key = (r.get("os","?"), r.get("runner","?"))
    d = by_key[key]
    d["os"], d["runner"] = key
    t = r.get("type","")
    if t=="cold": d["cold"].append(float(r.get("seconds",0)))
    if t=="warm": d["warm"].append(float(r.get("seconds",0)))
lines=[]
lines.append("# CI speed benchmarks (receipt-backed)\\n")
lines.append("All entries are medians over attested runs from `.tau_ledger/bench/runs.ndjson`. The acceleration factor is cold/warm.\\n")
lines.append("| OS | Runner | N(cold) | median_cold_s | N(warm) | median_warm_s | factor (cold/warm) |\\n")
lines.append("|---|---|---:|---:|---:|---:|---:|\\n")
for (osname, runner), d in sorted(by_key.items()):
    nc, nw = len(d["cold"]), len(d["warm"])
    mc = statistics.median(d["cold"]) if nc else 0.0
    mw = statistics.median(d["warm"]) if nw else 0.0
    fac = (mc/mw) if (mw>0) else 0.0
    lines.append(f"| {osname} | {runner} | {nc} | {mc:.2f} | {nw} | {mw:.2f} | {fac:.2f} |\\n")
with open(out,"w",encoding="utf-8") as g: g.writelines(lines)
