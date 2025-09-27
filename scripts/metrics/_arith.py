import math
def phi(n:int)->int:
    if n<=1: return 1
    m=n; p=2; acc=1
    while p*p<=m:
        if m%p==0:
            acc*=p-1
            while m%p==0: m//=p
        p+=1
    if m>1: acc*=m-1
    return acc
def sigma(n:int)->int:
    if n<=0: return 0
    m=n; p=2; acc=1
    while p*p<=m:
        if m%p==0:
            t=1; powp=1
            while m%p==0:
                powp*=p; t+=powp; m//=p
            acc*=t
        p+=1
    if m>1: acc*=1+m
    return acc
def omega(n:int)->float:
    s=sigma(n); return 0.0 if s==0 else phi(n)/s
