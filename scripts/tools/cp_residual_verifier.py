#!/usr/bin/env python3
import json,sys,math,hashlib,time
def die(msg): print(json.dumps({"ok":False,"error":msg}), flush=True); sys.exit(0)
def sha256_obj(o):
  return hashlib.sha256(json.dumps(o,sort_keys=True,separators=(",",":")).encode()).hexdigest()
def jacobi_sym_3x3(A, itmax=50, tol=1e-12):
  V=[[1.0,0.0,0.0],[0.0,1.0,0.0],[0.0,0.0,1.0]]
  for _ in range(itmax):
    p,q, m = 0,1,0.0
    for i in range(3):
      for j in range(i+1,3):
        if abs(A[i][j])>m: m=abs(A[i][j]); p,q=i,j
    if m<tol: break
    app,aqq,apq = A[p][p],A[q][q],A[p][q]
    phi=0.5*math.atan2(2*apq, (aqq-app))
    c,s=math.cos(phi), math.sin(phi)
    for k in range(3):
      A_pk, A_qk = A[p][k], A[q][k]
      A[p][k]=A[k][p]=c*A_pk - s*A_qk
      A[q][k]=A[k][q]=s*A_pk + c*A_qk
    A[p][p]=c*c*app - 2*s*c*apq + s*s*aqq
    A[q][q]=s*s*app + 2*s*c*apq + c*c*aqq
    A[p][q]=A[q][p]=0.0
    for k in range(3):
      V_pk, V_qk = V[p][k], V[q][k]
      V[p][k]=c*V_pk - s*V_qk
      V[q][k]=s*V_pk + c*V_qk
  return A, V
def pmns_angles(U):
  s13=abs(U[0][2]); th13=math.asin(max(0.0,min(1.0,s13))); c13=max(1e-12, math.sqrt(max(0.0,1.0-s13*s13)))
  th12=math.atan2(abs(U[0][1]), abs(U[0][0]))
  th23=math.atan2(abs(U[1][2]), abs(U[2][2]))
  return {"theta12_deg": th12*180/math.pi, "theta13_deg": th13*180/math.pi, "theta23_deg": th23*180/math.pi, "delta_deg": 0.0}
if len(sys.argv)!=2: die("usage")
spec=json.load(open(sys.argv[1],'r',encoding='utf-8'))
mnu=spec.get("mnu"); bounds=spec.get("bounds",{})
if not mnu or len(mnu)!=3: die("bad_mnu")
A=[[float(mnu[i][j]) for j in range(3)] for i in range(3)]
for i in range(3):
  for j in range(3):
    if abs(A[i][j]-A[j][i])>1e-9: die("mnu_not_symmetric")
_, U = jacobi_sym_3x3([row[:] for row in A])
ang=pmns_angles(U)
def within(x,lo,hi): return (x>=lo and x<=hi)
res={
 "theta12_deg": {"obs":ang["theta12_deg"], "exp":[bounds.get("theta12_min",0), bounds.get("theta12_max",90)]},
 "theta13_deg": {"obs":ang["theta13_deg"], "exp":[bounds.get("theta13_min",0), bounds.get("theta13_max",90)]},
 "theta23_deg": {"obs":ang["theta23_deg"], "exp":[bounds.get("theta23_min",0), bounds.get("theta23_max",90)]},
 "delta_deg":   {"obs":ang["delta_deg"],   "exp":[bounds.get("delta_min",-180), bounds.get("delta_max",180)]}
}
ok=True
for v in res.values(): ok = ok and within(v["obs"], v["exp"][0], v["exp"][1])
out={"ok": ok, "kind":"tau-crystal.physics.cp_residual",
     "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
     "input_sha256": sha256_obj(spec), "angles": ang, "checks": res}
print(json.dumps(out,separators=(",",":"),ensure_ascii=True))
