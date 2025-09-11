#!/usr/bin/env python3
import json,sys,math,hashlib,time
def sha(o): import hashlib,json; return hashlib.sha256(json.dumps(o,sort_keys=True,separators=(",",":")).encode()).hexdigest()
def tbm():
  return [
    [ (2/3)**0.5,  1/3**0.5, 0.0 ],
    [ -(1/6)**0.5, 1/3**0.5, 1/2**0.5 ],
    [  (1/6)**0.5,-1/3**0.5, 1/2**0.5 ],
  ]
def r13(theta):
  c=math.cos(theta); s=math.sin(theta)
  return [[c,0.0,s],[0.0,1.0,0.0],[-s,0.0,c]]
def mmul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def angles(U):
  s13=abs(U[0][2]); th13=math.asin(max(0.0,min(1.0,s13)))
  th12=math.atan2(abs(U[0][1]), abs(U[0][0]))
  th23=math.atan2(abs(U[1][2]), abs(U[2][2]))
  return dict(theta12_deg=th12*180/math.pi, theta13_deg=th13*180/math.pi, theta23_deg=th23*180/math.pi, delta_deg=0.0)
def within(x,lo,hi): return (x>=lo and x<=hi)
if len(sys.argv)!=2: print(json.dumps({"ok":False,"error":"usage"})); sys.exit(0)
spec=json.load(open(sys.argv[1],'r',encoding='utf-8'))
scheme=spec.get("scheme"); th_deg=float(spec.get("theta_deg",9.0)); bounds=spec.get("bounds",{})
if scheme!="tbm_r13": print(json.dumps({"ok":False,"error":"bad_scheme"})); sys.exit(0)
U = mmul(r13(th_deg*math.pi/180.0), tbm())
ang=angles(U)
res={
 "theta12_deg":{"obs":ang["theta12_deg"],"exp":[bounds.get("theta12_min",0),bounds.get("theta12_max",90)]},
 "theta13_deg":{"obs":ang["theta13_deg"],"exp":[bounds.get("theta13_min",0),bounds.get("theta13_max",90)]},
 "theta23_deg":{"obs":ang["theta23_deg"],"exp":[bounds.get("theta23_min",0),bounds.get("theta23_max",90)]},
 "delta_deg":{"obs":ang["delta_deg"],"exp":[bounds.get("delta_min",-10),bounds.get("delta_max",10)]}
}
ok=True
for v in res.values(): ok = ok and within(v["obs"], v["exp"][0], v["exp"][1])
out={"ok":ok,"kind":"tau-crystal.physics.cp_unitary","timestamp":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime()),
     "input_sha256":sha(spec),"unitary_scheme":scheme,"theta_deg":th_deg,"angles":ang,"checks":res}
print(json.dumps(out,separators=(",",":"),ensure_ascii=True))
