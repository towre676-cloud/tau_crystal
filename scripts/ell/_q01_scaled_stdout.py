import os, sys, cmath, math
sys.path.insert(0, os.path.join(os.getcwd(),'scripts','ell'))
TWOPI=2*math.pi; ABS=1e-12
S = complex(0.184515305872, -19.2971825497)
def d5(z,tau,N):
    q=cmath.exp(2j*math.pi*tau); s0=s1=s2=s3=s4=s5=0j
    for m in range(-N,N+1):
        n=m+0.5; a=(((-1)**m)*(q**(n*n))*cmath.exp(1j*TWOPI*n*z)); f=1j*TWOPI*n
        s0+=a; s1+=a*f; s2+=a*(f*f); s3+=a*(f**3); s4+=a*(f**4); s5+=a*(f**5)
    fac=-1j; return fac*s0,fac*s1,fac*s2,fac*s3,fac*s4,fac*s5
def Cx_series(z,tau,N):
    A0,A1,A2,A3,A4,A5=d5(-z,tau,N); b0,b1,b2,b3,b4,b5=d5(0,tau,N)
    b0=0j; b2=0j; b4=0j
    a1=A1/A0; a2=A2/A0; a3=A3/A0; a4=A4/A0; a2c=a2/2.0; a3c=a3/6.0; a4c=a4/24.0
    alpha=b2/(2*b1) if b1!=0 else 0.0; beta=b3/(6*b1) if b1!=0 else 0.0
    gamma=b4/(24*b1) if b1!=0 else 0.0; delta=b5/(120*b1) if b1!=0 else 0.0
    inv1=-alpha; inv2=alpha*alpha-beta; inv3=-(alpha**3)+2*alpha*beta-gamma; inv4=(alpha**4)-3*(alpha**2)*beta+(beta**2)+2*alpha*gamma-delta
    s1=a1+inv1; s2=a2c+a1*inv1+inv2; s3=a3c+a2c*inv1+a1*inv2+inv3; s4=a4c+a3c*inv1+a2c*inv2+a1*inv3+inv4
    return ((1.0/(TWOPI*1j))**3)*s4
def Ell_scaled(tau,z,N): return S * (-600.0*Cx_series(z,tau,N))
def solve_pair(z,N,t1,t2):
    q1=cmath.exp(2j*math.pi*t1); q2=cmath.exp(2j*math.pi*t2)
    v1=Ell_scaled(t1,z,N); v2=Ell_scaled(t2,z,N)
    den=q1-q2; sc=max(abs(q1),abs(q2),1.0)
    if abs(den)<=ABS*sc: return None,None,'den~0'
    a1=(v1-v2)/den; a0=v1-a1*q1; return a0,a1,''
def f(x):\n    try: return f"{float(x):.12g}"\n    except: return 'NaN'
def main():
    N=360; t1=0.12+3.4j; t2=0.19+2.7j; zs=[0.21,0.25,0.31]
    print('\t'.join(['z','y.re','y.im','a0.re','a0.im','chi_y.re','chi_y.im','rel_q0','a1.re','a1.im','|q1|','|q2|','Note','scale.re','scale.im']))
    for z in zs:
        y=cmath.exp(2j*math.pi*z); chiy=-1.0/y+101.0
        a0,a1,note=solve_pair(z,N,t1,t2)
        q1=abs(cmath.exp(2j*math.pi*t1)); q2=abs(cmath.exp(2j*math.pi*t2))
        if a0 is None:\n            print('\t'.join([f(z),f(y.real),f(y.imag),'NaN','NaN',f(chiy.real),f(chiy.imag),'NaN','NaN','NaN',f(q1),f(q2),note,f(S.real),f(S.imag)])); continue
        rel=abs(a0-chiy)/(abs(chiy) if abs(chiy)>ABS else 1.0)
        print('\t'.join([f(z),f(y.real),f(y.imag),f(a0.real),f(a0.imag),f(chiy.real),f(chiy.imag),f(rel),f(a1.real),f(a1.imag),f(q1),f(q2),note,f(S.real),f(S.imag)]))
if __name__=='__main__': main()
