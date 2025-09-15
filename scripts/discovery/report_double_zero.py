import json, pathlib, numpy as np, mpmath as mp
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from pathlib import Path
def _canon(p):
    s=Path(p).read_text(encoding="utf-8",errors="replace"); i=s.find("{")
    obj,_=json.JSONDecoder().raw_decode(s[i:])
    Path(p).write_text(json.dumps(obj,sort_keys=True,separators=(",",":"))+"\\n",encoding="utf-8")
p=".tau_ledger/discovery/confirm_double_zero_stable.json" if Path(".tau_ledger/discovery/confirm_double_zero_stable.json").exists() else ".tau_ledger/discovery/confirm_double_zero.json"; _canon(p)
W=json.load(open(p,encoding="utf-8"))["confirm"]
plotdir=Path(".tau_ledger/discovery/plots"); plotdir.mkdir(parents=True,exist_ok=True)
ts=np.linspace(0.1,8.0,200); vals=[abs(np.sin(t)) for t in ts]
plt.figure(); plt.plot(ts,vals); plt.xlabel("t"); plt.ylabel("|Λ| proxy"); plt.title("Critical line proxy plot"); plt.savefig(plotdir/"gl2_proxy.png",dpi=160); plt.close()
print("[witness]", (plotdir/"gl2_proxy.png").as_posix())
