#!/usr/bin/env python3
import sys, json, os
wd=sys.argv[1]; out=sys.argv[2]
raw=json.load(open(os.path.join(wd,"raw","fiber_raw.json"),"r",encoding="utf-8"))
payload={
 "geometry":raw.get("geometry",{}),
 "grid":raw.get("grid",{}),
 "multiplier":{"char":raw.get("mult_char","trivial"),"index":"3/2","label":"theta","level":raw.get("level",1)},
 "normalization":{"chi":raw.get("geometry",{}).get("chi"),"ell_tau0":raw.get("slices",{}).get("tau0")},
 "coeffs":raw.get("coeffs",{}),
 "rademacher":{"polars":raw.get("polars",[]),"termination":raw.get("polar_cert",{})},
 "mde_cert":raw.get("mde_cert",{}),
 "sturm_cert":raw.get("sturm_cert",{}),
 "window":{"nmax":raw.get("nmax",120),"rmax":raw.get("rmax",6)}
}
open(out,"w",encoding="utf-8",newline="\n").write(json.dumps(payload,sort_keys=True,separators=(",",":")))
