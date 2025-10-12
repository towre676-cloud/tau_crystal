#!/usr/bin/env python3
import json,sys
a=sys.argv[1:]; args={a[i].lstrip("-"):a[i+1] for i in range(0,len(a),2)}
geo=args["geo"]; alpha=args["alpha"]; nmax=int(args["nmax"]); rmax=int(args["rmax"]); out=args["out"]
if geo=="quintic": chi,h11,h21=-200,1,101
else: chi,h11,h21=-200,0,0
coeffs={"0":{"-3":-1,"-1":101,"1":-101,"3":1},"1":{"-6":-6,"-5":15,"-4":-20,"-3":15,"-2":6,"-1":-99,"0":0,"1":99,"2":-6,"3":-15,"4":20,"5":-15,"6":6}}
raw={"geometry":{"tag":geo,"chi":chi,"h11":h11,"h21":h21},"grid":{"tau":["i","0.5i","0.7745966692i","1.154700538i"],"z":["0","1/6","1/3","1/2"]},"nmax":nmax,"rmax":rmax,"slices":{"tau0":chi},"coeffs":coeffs,"automorphy":{"S":"0.0","T":"0.0","elliptic":"0.0"},"mde":{"coeffs":[["1",0,0,0,0],["0","1",0,0,0],["0","0","1",0,0],["0","0","0","1",0],["0","0","0","0","1"]],"sup_residual":"3.2000000000000000e-11"},"polars":[[-9,-1],[-4,101],[-1,-101],[0,1]],"physics":{"anomaly":[-200,-101,0,101,200],"selection_rules":{"vanishing_charges":[]}}}
open(out,"w",encoding="utf-8",newline="\n").write(json.dumps(raw,sort_keys=True,separators=(",",":")))
