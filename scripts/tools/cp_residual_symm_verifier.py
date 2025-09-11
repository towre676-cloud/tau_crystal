#!/usr/bin/env python3
import json,sys,math,hashlib,time

def sha(o): return hashlib.sha256(json.dumps(o,sort_keys=True,separators=(",",":")).encode()).hexdigest()
def now(): return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())

def dagger(A): return [[A[j][i].conjugate() for j in range(3)] for i in range(3)]
def mmul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def eye(): return [[1+0j,0+0j,0+0j],[0+0j,1+0j,0+0j],[0+0j,0+0j,1+0j]]

def is_unitary(U,tol=1e-10):
  I=eye(); UH_U=mmul(dagger(U),U)
  return max(abs(UH_U[i][j]-I[i][j]) for i in range(3) for j in range(3))<tol

def mat_pow(A,n):
  R=eye()
  for _ in range(n): R=mmul(R,A)
  return R

def tbm():
  r23=(2/3)**0.5; r13=(1/3)**0.5; r12=(1/6)**0.5; r12p=(1/2)**0.5
  return [
    [ r23,   r13,    0.0 ],
    [ -r12,  r13,    r12p ],
    [  r12, -r13,    r12p ],
  ]
def tbm_cols():
  U=tbm()
  return [complex(U[i][0]) for i in range(3)], [complex(U[i][1]) for i in range(3)], [complex(U[i][2]) for i in range(3)]
def colcomb(a,b,ca,sa):
  c1=[ca*a[i]+sa*b[i] for i in range(3)]
  c2=[-sa*a[i]+ca*b[i] for i in range(3)]
  return c1,c2
def from_cols(c1,c2,c3):
  return [ [c1[0],c2[0],c3[0]], [c1[1],c2[1],c3[1]], [c1[2],c2[2],c3[2]] ]

def R13(theta):
  c=math.cos(theta); s=math.sin(theta)
  return [[c+0j,0+0j,s+0j],[0+0j,1+0j,0+0j],[-s+0j,0+0j,c+0j]]
def R23(theta):
  c=math.cos(theta); s=math.sin(theta)
  return [[1+0j,0+0j,0+0j],[0+0j,c+0j,s+0j],[0+0j,-s+0j,c+0j]]

def pmns_angles(U):
  s13=abs(U[0][2]); th13=math.asin(max(0.0,min(1.0,s13)))
  th12=math.atan2(abs(U[0][1]), max(1e-15,abs(U[0][0])))
  th23=math.atan2(abs(U[1][2]), max(1e-15,abs(U[2][2])))
  return dict(theta12_deg=th12*180/math.pi, theta13_deg=th13*180/math.pi, theta23_deg=th23*180/math.pi, delta_deg=0.0)

def build_from_templates(templates, params):
  th13 = float(params.get("theta13_deg", 9.0))*math.pi/180.0
  ω = complex(math.cos(2*math.pi/3), math.sin(2*math.pi/3))

  if templates.get("Ge") != "Z3_TBM":
    raise ValueError("unsupported Ge template")
  Ue = [[complex(x) for x in row] for row in tbm()]
  Dω = [[1+0j,0+0j,0+0j],[0+0j,ω,0+0j],[0+0j,0+0j,ω.conjugate()]]
  Ge = mmul(mmul(Ue,Dω),dagger(Ue))

  Gnu_t = templates.get("Gnu")
  if Gnu_t == "Z2_mu_tau_with_CP":
    Uv = mmul(R13(th13), R23(math.pi/4.0))
  elif Gnu_t == "Z2_mu_tau_reflection":
    P=[[1+0j,0+0j,0+0j],[0+0j,0+1j,0+0j],[0+0j,0+0j,-0-1j]]
    Uv = mmul(R23(math.pi/4.0), mmul(P, R13(th13)))
  elif Gnu_t == "TM1":
    beta = float(params.get("beta_deg", 9.0))*math.pi/180.0
    cb,sb=math.cos(beta),math.sin(beta)
    c1,c2,c3=tbm_cols()
    c2p,c3p = colcomb(c2,c3,cb,sb)
    Uv = from_cols(c1,c2p,c3p)
  elif Gnu_t == "TM2":
    beta = float(params.get("beta_deg", 9.0))*math.pi/180.0
    cb,sb=math.cos(beta),math.sin(beta)
    c1,c2,c3=tbm_cols()
    c1p,c3p = colcomb(c1,c3,cb,sb)
    Uv = from_cols(c1p,c2,c3p)
  else:
    raise ValueError("unsupported Gnu template")

  D_z2 = [[1+0j,0+0j,0+0j],[0+0j,-1+0j,0+0j],[0+0j,0+0j,1+0j]]
  S = mmul(mmul(Uv,D_z2),dagger(Uv))
  X = [[1+0j,0+0j,0+0j],[0+0j,0+0j,1+0j],[0+0j,1+0j,0+0j]]
  return Ue,Uv,Ge,S,X

def witness_checks(Ue,Uv,Ge,S,X):
  I=eye(); checks={}
  checks["Ue_unitary"]=is_unitary(Ue); checks["Uv_unitary"]=is_unitary(Uv)
  checks["Ge_unitary"]=is_unitary(Ge); checks["S_unitary"]=is_unitary(S)

  Ge3=mat_pow(Ge,3); S2=mat_pow(S,2); X2=mat_pow(X,2)
  checks["Ge_order3"]=max(abs(Ge3[i][j]-I[i][j]) for i in range(3) for j in range(3))<1e-9
  checks["S_order2"]=max(abs(S2[i][j]-I[i][j]) for i in range(3) for j in range(3))<1e-9
  checks["X_symmetric"]=all(abs(X[i][j]-X[j][i])<1e-12 for i in range(3) for j in range(3))
  checks["X_unitary"]=is_unitary(X)
  checks["X_order2"]=max(abs(X2[i][j]-I[i][j]) for i in range(3) for j in range(3))<1e-9

  UH_Ge_U = mmul(mmul(dagger(Ue),Ge),Ue)
  off1=sum(abs(UH_Ge_U[i][j]) for i in range(3) for j in range(3) if i!=j)
  checks["Ge_diagonalized_by_Ue"] = (off1<1e-8)

  UH_SU = mmul(mmul(dagger(Uv),S),Uv)
  off2=sum(abs(UH_SU[i][j]) for i in range(3) for j in range(3) if i!=j)
  checks["S_diagonalized_by_Uv"] = (off2<1e-8)

  # μ–τ reflection modulus equality (on full PMNS)
  U = mmul(dagger(Ue), Uv)
  mt_ok=True
  for j in range(3):
    if abs(abs(U[1][j])-abs(U[2][j]))>1e-6:
      mt_ok=False; break
  checks["mu_tau_moduli_equal"]=mt_ok

  # TM1/TM2 preserved-column modulus witnesses (on full PMNS)
  c1,c2,c3=tbm_cols()
  cols=[[U[0][0],U[1][0],U[2][0]],[U[0][1],U[1][1],U[2][1]],[U[0][2],U[1][2],U[2][2]]]
  tbm_mod=[[abs(c1[0]),abs(c1[1]),abs(c1[2])],
           [abs(c2[0]),abs(c2[1]),abs(c2[2])],
           [abs(c3[0]),abs(c3[1]),abs(c3[2])]]
  checks["tm1_preserved_col1"]=all(abs(abs(cols[0][i])-tbm_mod[0][i])<1e-4 for i in range(3))
  checks["tm2_preserved_col2"]=all(abs(abs(cols[1][i])-tbm_mod[1][i])<1e-4 for i in range(3))
  return checks

def within(x,lo,hi): return (x>=lo and x<=hi)

def main():
  if len(sys.argv)!=2:
    print(json.dumps({"ok":False,"error":"usage"})); return
  spec=json.load(open(sys.argv[1],'r',encoding='utf-8'))
  templates=spec.get("templates",{}); params=spec.get("parameters",{}); bounds=spec.get("bounds",{})
  assumptions=spec.get("assumptions",{"taken_as_given":[], "to_test":[]})

  Ue,Uv,Ge,S,X = build_from_templates(templates,params)
  U = mmul(dagger(Ue),Uv)
  ang = pmns_angles(U)
  w = witness_checks(Ue,Uv,Ge,S,X)

  checks = {
    "theta12_deg":{"obs":ang["theta12_deg"],"exp":[bounds.get("theta12_min",0),bounds.get("theta12_max",90)]},
    "theta13_deg":{"obs":ang["theta13_deg"],"exp":[bounds.get("theta13_min",0),bounds.get("theta13_max",90)]},
    "theta23_deg":{"obs":ang["theta23_deg"],"exp":[bounds.get("theta23_min",0),bounds.get("theta23_max",90)]},
    "delta_deg":{"obs":ang["delta_deg"],"exp":[bounds.get("delta_min",-10),bounds.get("delta_max",10)]}
  }
  gate_ok = all(within(v["obs"],v["exp"][0],v["exp"][1]) for v in checks.values())
  overall_ok = gate_ok and all(w.values())

  out={
    "ok": overall_ok,
    "kind":"tau-crystal.physics.cp_residual_symm",
    "timestamp": now(),
    "input_sha256": sha(spec),
    "assumptions":{"taken_as_given":assumptions.get("taken_as_given",[]),"to_test":assumptions.get("to_test",[])},
    "templates": templates, "parameters": params,
    "angles": ang, "checks": checks, "witness": w
  }
  print(json.dumps(out,separators=(",",":"),ensure_ascii=True))

if __name__=="__main__":
  main()
