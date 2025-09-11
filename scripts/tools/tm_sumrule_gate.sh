#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
IN="${1:-}"; OUT="${2:-}"
[ -n "${IN}" ] && [ -n "${OUT}" ] && [ -f "${IN}" ] || { printf '{"ok":false,"error":"usage: tm_sumrule_gate.sh <in.json> <out.json)"}\n' > "${OUT:-/dev/stdout}"; exit 2; }
command -v python3 >/dev/null 2>&1 || { printf '{"ok":false,"error":"python3_not_found"}\n' > "$OUT"; exit 0; }
python3 - "$IN" <<'PY' > "$OUT"
import json,sys,math,hashlib,datetime
d=json.load(open(sys.argv[1],'r',encoding='utf-8'))
templ=(d.get("templates") or {})
gnu=templ.get("Gnu","")
pars=(d.get("parameters") or {})
th13=float(pars.get("theta13_deg",9.0))
bounds=(d.get("bounds") or {})
tmin=float(bounds.get("theta12_min",0))
tmax=float(bounds.get("theta12_max",90))
tol=float(d.get("sum_rule_tol", 1e-3))
# hashes
inp_hash=hashlib.sha256(json.dumps(d,sort_keys=True,separators=(",",":")).encode()).hexdigest()
# compute feasibility: TM1 cosθ12 cosθ13 = sqrt(2/3); TM2 sinθ12 cosθ13 = 1/sqrt(3)
c13=math.cos(math.radians(th13))
lhs=rhs=req=None
ok=False; reason=None; theta12_req=None
if gnu=="TM1":
    rhs=math.sqrt(2.0/3.0)
    val=rhs/c13
    if abs(val)<=1.0:
        theta12_req=math.degrees(math.acos(val))
        err=abs(math.cos(math.radians(theta12_req))*c13 - rhs)
        ok = (tmin<=theta12_req<=tmax) and (err<=tol)
    else:
        ok=False
    lhs="cos(theta12)*cos(theta13)"
elif gnu=="TM2":
    rhs=1.0/math.sqrt(3.0)
    val=rhs/c13
    if abs(val)<=1.0:
        theta12_req=math.degrees(math.asin(val))
        err=abs(math.sin(math.radians(theta12_req))*c13 - rhs)
        ok = (tmin<=theta12_req<=tmax) and (err<=tol)
    else:
        ok=False
    lhs="sin(theta12)*cos(theta13)"
else:
    # for non-TM templates we pass-through as not-applicable (green)
    print(json.dumps({
      "ok": True,
      "kind": "tau-crystal.physics.tm_sumrule",
      "timestamp": datetime.datetime.utcnow().replace(microsecond=0).isoformat()+"Z",
      "input_sha256": inp_hash,
      "template": gnu,
      "applicable": False
    }, separators=(",",":"))); sys.exit(0)

out={
  "ok": ok,
  "kind": "tau-crystal.physics.tm_sumrule",
  "timestamp": datetime.datetime.utcnow().replace(microsecond=0).isoformat()+"Z",
  "input_sha256": inp_hash,
  "template": gnu,
  "theta13_deg": th13,
  "theta12_required_deg": theta12_req,
  "bounds": {"theta12_min": tmin, "theta12_max": tmax},
  "sum_rule": {"lhs": lhs, "rhs": rhs, "abs_err_tol": tol}
}
if not ok:
  out["error"]="sum_rule_violation_pre"
print(json.dumps(out, separators=(",",":")))
PY
