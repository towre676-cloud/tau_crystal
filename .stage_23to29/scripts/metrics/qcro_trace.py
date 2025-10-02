import json,sys,math
from ._arith import phi,sigma
def gamma_pulse(i:int,j:int,gamma0:float=1.0)->float:
    if i<=0 or j<=0: return 0.0
    g=math.gcd(i,j); L=(i*j)//g if g>0 else 0
    if g==0 or L==0: return 0.0
    ph=phi(g); sg=sigma(g)
    return 0.0 if ph==0 else gamma0*(g/L)*(sg/ph)
if __name__=='__main__':
    i=int(sys.argv[1]); j=int(sys.argv[2])
    print(json.dumps({'i':i,'j':j,'gamma':gamma_pulse(i,j)}))
