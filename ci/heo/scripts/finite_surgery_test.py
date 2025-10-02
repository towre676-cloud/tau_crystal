#!/usr/bin/env python3
def seq(values, fill=0):
    L=len(values)
    return lambda n: values[n-1] if n<=L else fill

def limsup(X, N=200000, w=5000):
    best=0; s=0
    for n in range(1,N+1):
        s+=X(n)
        if n%w==0: best=max(best, s/n)
    return best

def main():
    a=[0,1,0,0,1,0,1] * 5000 + [0]*100
    b=a[:] ; b[:50]=[1]*50
    Xa=seq(a); Xb=seq(b)
    la=limsup(Xa); lb=limsup(Xb)
    print({"H_a":la,"H_b":lb})
    assert abs(la-lb) < 1e-6

if __name__=="__main__":
    main()
