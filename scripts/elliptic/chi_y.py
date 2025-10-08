#!/usr/bin/env python3
import json, os, sys
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
out_coeffs = os.path.join(ROOT, "out", "coeffs")
os.makedirs(out_coeffs, exist_ok=True)
chi_y = {"geometry":"quintic","h11":1,"h21":101,"chi":-200,
         "q0_coeffs":{"3":1,"1":-101,"-1":101,"-3":-1}}
with open(os.path.join(out_coeffs,"chi_y_quintic.json"),"w") as f: json.dump(chi_y,f,indent=2)
print("chi_y written:", os.path.join(out_coeffs,"chi_y_quintic.json"))
