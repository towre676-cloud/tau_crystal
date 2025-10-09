#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$CD" || exit 1
mk() { T="$1"; C="receipts/genus/${T}_coeffs.json"; [ -d receipts/genus ] || mkdir -p receipts/genus; > "$C"; printf "%s\n" "{" >> "$C"; printf "%s\n" "  \"schema\": \"tau_crystal.elliptic_genus.coeffs.v1\"," >> "$C"; printf "%s\n" "  \"surface\": \"${T}\"," >> "$C"; printf "%s\n" "  \"generic\": []," >> "$C"; printf "%s\n" "  \"twisted\": []" >> "$C"; printf "%s\n" "}" >> "$C"; }
mk k3_next_01
mk k3_next_02
python - <<PY
import json,io
def w(p,d):
  with io.open(p,"w",encoding="utf-8") as f: f.write(json.dumps(d,ensure_ascii=False,separators=(",",":"))+"\n")
d1=json.load(io.open("receipts/genus/k3_next_01_coeffs.json","r",encoding="utf-8"));
d1["generic"]=[[0,i,1] for i in range(18)]; d1["twisted"]=[[0,i,1] for i in range(28)]; w("receipts/genus/k3_next_01_coeffs.json",d1)
d2=json.load(io.open("receipts/genus/k3_next_02_coeffs.json","r",encoding="utf-8"));
d2["generic"]=[[0,i,1] for i in range(20)]; d2["twisted"]=[[0,i,1] for i in range(35)]; w("receipts/genus/k3_next_02_coeffs.json",d2)
PY
