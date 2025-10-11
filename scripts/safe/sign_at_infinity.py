import sys,io,json,decimal
decimal.getcontext().prec = 200
p,out = sys.argv[1], sys.argv[2]
D = json.load(io.open(p,"r",encoding="utf-8"))
C = D.get("curve",{})
def ZZ(x,default="0"):
    if x is None: x=default
    return decimal.Decimal(str(x))
a1=ZZ(C.get("a1"),"1"); a2=ZZ(C.get("a2"),"0"); a3=ZZ(C.get("a3"),"0"); a4=ZZ(C.get("a4"),"0"); a6=ZZ(C.get("a6"),"0")
b2 = a1*a1 + 4*a2
b4 = 2*a4 + a1*a3
b6 = a3*a3 + 4*a6
b8 = a1*a1*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3*a3 - a4*a4
Delta = -b2*b2*b8 - 8*b4*b4*b4 - 27*b6*b6 + 9*b2*b4*b6
sgn = "-1" if Delta < 0 else "+1"
D.setdefault("curve",{}).update({"discriminant_sign": sgn})
io.open(p,"w",encoding="utf-8").write(json.dumps(D,ensure_ascii=False,separators=(",",":"))+"\n")
io.open(out,"w",encoding="utf-8").write(json.dumps({"Delta":str(Delta),"sign":sgn},separators=(",",":"))+"\n")
