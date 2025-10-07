import cmath, math
TWOPI = 2.0*math.pi
def _theta1_derivs5(z,tau,N):
    q = cmath.exp(2j*math.pi*tau)
    s0=s1=s2=s3=s4=s5=0j
    for m in range(-N,N+1):
        n = m + 0.5
        a = ((-1)**m) * (q**(n*n)) * cmath.exp(1j*TWOPI*n*z)
        f = 1j*TWOPI*n
        s0 += a; s1 += a*f; s2 += a*(f*f); s3 += a*(f**3); s4 += a*(f**4); s5 += a*(f**5)
    fac = (-1j)
    return fac*s0, fac*s1, fac*s2, fac*s3, fac*s4, fac*s5
def Cx_cubic(z,tau,N):
    # Expand in u = x/(2πi) at u=0 with z fixed.
    A0,A1,A2,A3,A4,A5 = _theta1_derivs5(-z,tau,N)
    b0,b1,b2,b3,b4,b5 = _theta1_derivs5( 0,tau,N)
    b0=0j; b2=0j; b4=0j  # θ1 is odd at 0
    # Ahat = 1 + a1 u + a2 u^2/2 + a3 u^3/6 + a4 u^4/24
    a1=A1/A0; a2=A2/A0; a3=A3/A0; a4=A4/A0
    a2c=a2/2.0; a3c=a3/6.0; a4c=a4/24.0
    # Bhat = B/(b1 u) = 1 + α u + β u^2 + γ u^3 + δ u^4
    alpha=b2/(2*b1) if b1!=0 else 0.0
    beta =b3/(6*b1) if b1!=0 else 0.0
    gamma=b4/(24*b1) if b1!=0 else 0.0
    delta=b5/(120*b1) if b1!=0 else 0.0
    inv1=-alpha
    inv2=alpha*alpha - beta
    inv3=-(alpha**3) + 2*alpha*beta - gamma
    inv4=(alpha**4) - 3*(alpha**2)*beta + (beta**2) + 2*alpha*gamma - delta
    s1=a1 + inv1
    s2=a2c + a1*inv1 + inv2
    s3=a3c + a2c*inv1 + a1*inv2 + inv3
    s4=a4c + a3c*inv1 + a2c*inv2 + a1*inv3 + inv4
    # Φ(u)=(1/u)S(u), Φ_reg=(S-1)/u ⇒ coeff[u^3] = +s4; d/dx=(1/(2πi))d/du
    return ((1.0/(TWOPI*1j))**3) * s4
