#!/usr/bin/env python3
import json, argparse

def periodic(patt):
    T=len(patt)
    return lambda n: patt[(n-1)%T]

def limsup(X, N=200000, w=5000):
    best=0; s=0
    for n in range(1,N+1):
        s+=X(n)
        if n%w==0:
            best=max(best, s/n)
    return best

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--sequence", required=True)
    ap.add_argument("--thinning", required=True)
    args=ap.parse_args()
    obj=json.load(open(args.sequence))
    patt=obj["pattern"]
    X=periodic(patt)
    thin=json.load(open(args.thinning))
    iota=lambda n: thin[str(n)]
    alpha = min(n/iota(n) for n in range(1, min(5000,len(thin))+1))
    def Xthin(n): return X(iota(n))
    lhs=limsup(X)
    rhs=alpha*limsup(Xthin)
    print(json.dumps({"alpha_lower_bound":alpha, "H":lhs, "alpha*H_thin":rhs}))
    assert lhs + 1e-9 >= rhs

if __name__=="__main__":
    main()
