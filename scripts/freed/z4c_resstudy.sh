#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LED=".tau_ledger/freed"; mkdir -p "$LED"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
CSV="$LED/z4c_resstudy_${STAMP}.csv"; JSON="$LED/z4c_resstudy_${STAMP}.json"

TEST="${1:-gauge}"; shift || true
RES_LIST=("$@"); [ ${#RES_LIST[@]} -gt 0 ] || RES_LIST=(801 1201 1601)

python - "$TEST" "$CSV" "$JSON" "${RES_LIST[@]}" <<'PY'
import json, subprocess, sys, math, os, numpy as np
test, csvp, jsonp, res_list = sys.argv[1], sys.argv[2], sys.argv[3], list(map(int, sys.argv[4:]))

def run_one(res, glued):
  out = subprocess.check_output(
    [sys.executable,"scripts/freed/z4c_nonlinear_1d.py","--test",test,"--res",str(res),"--glued",str(glued)] + os.environ.get("Z4C_ARGS","").split(),
    text=True).strip()
  with open(out,"r",encoding="utf-8") as f: r=json.load(f)
  F=r["norms"]["final"]; I=r["norms"]["integrated"]
  fin_ok = all(np.isfinite([F["H"],F["M"],F["C_Gamma"]]))
  int_ok = all(np.isfinite([I["H"],I["M"],I["C_Gamma"]]))
  stable = bool(r["stable"] and fin_ok and int_ok)
  return dict(res=res, glued=bool(glued), stable=stable,
              H=F["H"] if fin_ok else None,
              M=F["M"] if fin_ok else None,
              C_Gamma=F["C_Gamma"] if fin_ok else None,
              IH=I["H"] if int_ok else None,
              IM=I["M"] if int_ok else None,
              ICG=I["C_Gamma"] if int_ok else None,
              path=out)

rows=[]
for r in res_list:
  rows.append(dict(step=run_one(r, False), glued=run_one(r, True)))

with open(csvp,"w",encoding="utf-8") as f:
  f.write("res,H_step,H_glued,M_step,M_glued,C_Gamma_step,C_Gamma_glued,IH_step,IH_glued,IM_step,IM_glued,ICG_step,ICG_glued,st_step,st_glued\n")
  for rec in rows:
    s,g = rec["step"], rec["glued"]
    f.write(",".join(map(str,[
      s["res"], s["H"], g["H"], s["M"], g["M"], s["C_Gamma"], g["C_Gamma"],
      s["IH"], g["IH"], s["IM"], g["IM"], s["ICG"], g["ICG"],
      int(s["stable"]), int(g["stable"])
    ]))+"\n")

def finite_pos(xs): return [(1.0/(r-1), x) for r,x in zip(res_list,xs) if (x is not None and math.isfinite(x) and x>0.0)]
def order_from(triples):
  if len(triples) < 3: return None
  (h1,E1),(h2,E2),(h3,E3) = triples[-3:]
  return math.log(E2/E3)/math.log(h2/h3)

H_step  = [ rec["step"]["IH"]  for rec in rows ]
M_step  = [ rec["step"]["IM"]  for rec in rows ]
C_step  = [ rec["step"]["ICG"] for rec in rows ]

I_orders = dict(
  H = order_from(finite_pos(H_step)),
  M = order_from(finite_pos(M_step)),
  C_Gamma = order_from(finite_pos(C_step)),
)

deltas=[]
for rec in rows:
  s,g=rec["step"],rec["glued"]
  def d(a,b): return (None if (a is None or b is None) else (a-b))
  deltas.append(dict(
    res=s["res"], IH=d(s["IH"],g["IH"]), IM=d(s["IM"],g["IM"]), ICG=d(s["ICG"],g["ICG"]),
    H=d(s["H"],g["H"]), M=d(s["M"],g["M"]), C_Gamma=d(s["C_Gamma"],g["C_Gamma"])
  ))

stable = all(rec["step"]["stable"] and rec["glued"]["stable"] for rec in rows)

with open(jsonp,"w",encoding="utf-8") as f:
  json.dump(dict(stamp=os.path.basename(jsonp)[13:28], test=test,
                 I_orders=I_orders, deltas=deltas, stable=stable,
                 resolutions=res_list, csv=csvp), f, indent=2)
print(csvp); print(jsonp)
PY
