import sys,json,math
from math import log, pi
def gamma_R(s): # crude Γ_R(s)=π^{-s/2}Γ(s/2); use math.lgamma
    return math.exp(math.lgamma(s/2.0) - (s/2.0)*math.log(pi))
def L_completed(s, local):
    # toy Euler product truncation using local factors a_p; NOT rigorous — diagnostic only
    acc=1.0
    for term in local:
        p=term.get("p"); ap=term.get("a_p",0.0)
        if not p: continue
        z = p**(-s)
        # Sym^2 local factor approx: 1 - ap*z + p*z*z (coarse)
        denom = 1.0 - ap*z + (p*(z*z))
        if denom == 0: continue
        acc *= 1.0/denom
    return gamma_R(s+1.0)*gamma_R(s)*acc
def brent_zero(f,a,b,fa=None,fb=None,eps=1e-6,maxit=100):
    if fa is None: fa=f(a);
    if fb is None: fb=f(b);
    if fa*fb>0: return None
    c=a; fc=fa; d=e=b-a
    for _ in range(maxit):
        if abs(fc)<abs(fb): a,b,c=b,c,a; fa,fb,fc=fb,fc,fa
        tol=2.0*eps*abs(b)+0.5*eps; m=0.5*(c-b)
        if abs(m)<=tol or fb==0: return b
        if abs(e)<tol or abs(fa)<=abs(fb): d=e=m
        else:
            s=fb/fa; if a==c: p=2*m*s; q=1-s
            else:
                q=fa/fc; r=fb/fc; p=s*(2*m*q*(q-r)-(b-a)*(r-1)); q=(q-1)*(r-1)*(s-1)
            if p>0: q=-q; p=abs(p)
            if 2*p < min(3*m*q-abs(tol*q), abs(e*q)):
                e=d; d=p/q
            else:
                d=e=m
        a,fa=b,fb
        if abs(d)>tol: b += d
        else: b += tol if m>0 else -tol
        fb=f(b);
    return None
def main(curve,path):
    data=json.load(open(path,"rb"))
    local=data if isinstance(data,list) else data.get("local_factors",[])
    def f(t):
        s=0.5+1j*t
        val=L_completed(s, local)
        return val.real
    # scan small window for sign change, then Brent
    t0,t1,dt=-5.0,5.0,0.2
    prev_t=t0; prev_f=f(prev_t)
    zero=None
    t=prev_t+dt
    while t<=t1:
        ft=f(t)
        if prev_f==0 or ft==0 or (prev_f*ft)<0:
            zero=brent_zero(f,prev_t,t,prev_f,ft,eps=1e-6,maxit=200); break
        prev_t,prev_f=t,ft; t+=dt
    res={"curve":curve,"zero_t":zero}
    print(json.dumps(res))
if __name__=="__main__": main(sys.argv[1], sys.argv[2])
