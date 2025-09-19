import json,math,sys
lat=sys.argv[1] if len(sys.argv)>1 else ".tau_ledger/phys/lattice.json"
out=sys.argv[2] if len(sys.argv)>2 else ".tau_ledger/phys/debye_cap.txt"
L=json.load(open(lat,"r",encoding="utf-8"))
kx=L["force"]["kx"]; ky=L["force"]["ky"]; kz=L["force"]["kz"]; m=L["mass"]
K=(kx+ky+kz)/3.0; v=(K/m)**0.5; d=int(max(8,min(256, v*100.0)))
open(out,"w",encoding="utf-8").write(str(d)+"\n")
print(f"cap={d} (Kavg={K:.3f}, m={m:.3f})")
