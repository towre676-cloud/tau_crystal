import json,sys,math,cmath
def dft_power(v):
    n=len(v); P=[]
    for k in range(1,1+n//2):
        s=0j
        for t,x in enumerate(v): s+=x*cmath.exp(-2j*math.pi*k*t/n)
        P.append((k,(s.real*s.real+s.imag*s.imag)/n))
    return P
if __name__=='__main__':
    vals=[float(x) for x in sys.argv[1].split(',')]
    mu=sum(vals)/len(vals); v=[x-mu for x in vals]
    P=dft_power(v); E=sum(p for _,p in P) or 1.0
    print(json.dumps({'E':E,'power':P,'p':[p/E for _,p in P]}))
