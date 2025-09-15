import json,math,os,sys
lat_path=sys.argv[1] if len(sys.argv)>1 else ".tau_ledger/phys/lattice.json"
eps=float(os.environ.get("EPS","1e-6"))
K0=float(os.environ.get("K0","0.0"))  # optional pinning (on-site) term
L=json.load(open(lat_path,"r",encoding="utf-8"))
a=L["cell"]["a"]; b=L["cell"]["b"]; c=L["cell"]["c"]
kx=L["force"]["kx"]; ky=L["force"]["ky"]; kz=L["force"]["kz"]; m=L["mass"]
gmin=1e99
for ix in range(8):
    px=(ix/7.0)*math.pi
    for iy in range(8):
        py=(iy/7.0)*math.pi
        for iz in range(8):
            pz=(iz/7.0)*math.pi
            if K0==0.0 and ix==0 and iy==0 and iz==0:
                continue  # exclude Γ to avoid acoustic zero
            lamx=2*kx*(1.0-math.cos(px*a))
            lamy=2*ky*(1.0-math.cos(py*b))
            lamz=2*kz*(1.0-math.cos(pz*c))
            val=(lamx+lamy+lamz+K0)/m
            if val<gmin: gmin=val
print(f"gap_min={gmin:.12e} eps={eps:.3e} K0={K0:.3e}")
sys.exit(0 if gmin>eps else 4)
