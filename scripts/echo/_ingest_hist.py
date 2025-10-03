import json,csv,os
from pathlib import Path
def load():
    p=Path("data/qcro_counts.json")
    if p.exists():
        return json.loads(p.read_text())
    for name in ("data/qcro_counts.csv","data/qcro_counts.tsv"):
        if Path(name).exists():
            sep="," if name.endswith(".csv") else "\\t"
            with open(name,newline="") as f:
                r=csv.DictReader(f,delimiter=sep)
                for row in r: return row
    # fallback: prior echo placeholder
    try:
        return json.loads(Path("artifacts/echo/freq_hist.json").read_text())["freq"]
    except: return {"sigma":1,"phi":1,"rho":1}
raw=load()
sigma=float(raw.get("sigma",1.0)); phi=float(raw.get("phi",1.0)); rho=float(raw.get("rho",1.0))
s=sigma+phi+rho or 1.0
out={"freq":{"sigma":sigma,"phi":phi,"rho":rho},"weights":{"sigma":sigma/s,"phi":phi/s,"rho":rho/s}}
Path("artifacts/echo/freq_hist_norm.json").write_text(json.dumps(out,separators=(",",":")))
