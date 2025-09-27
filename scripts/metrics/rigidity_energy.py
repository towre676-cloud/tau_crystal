import json,sys
from ._arith import phi,sigma
def deltaE(n1:int,n2:int,W=None)->float:
    if n2<=n1: return 0.0
    if W is None: W=lambda n:1.0
    acc=0.0
    for k in range(n1+1,n2+1):
        p=phi(k); s=sigma(k)
        term=0.0 if p==0 else (s/p-1.0)*W(k)
        acc+=term
    return acc
if __name__=='__main__':
    n1=int(sys.argv[1]); n2=int(sys.argv[2])
    print(json.dumps({'n1':n1,'n2':n2,'deltaE':deltaE(n1,n2)}))
