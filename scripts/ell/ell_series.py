import cmath, os, sys
sys.path.insert(0, os.path.dirname(__file__))
def _theta1_and_derivs5(z,tau,N):
    twopi=2*cmath.pi; q=cmath.exp(2j*cmath.pi*tau)
    s0=s1=s2=s3=s4=s5=0j
    for m in range(-N,N+1):
        n=m+0.5
        a=(((-1)**m) * (q**(n*n)) * cmath.exp(1j*twopi*n*z))
        f=1j*twopi*n
        s0+=a; s1+=a*f; s2+=a*(f*f); s3+=a*(f*f*f); s4+=a*(f*f*f*f); s5+=a*(f*f*f*f*f)
    return (-1j)*s0, (-1j)*s1, (-1j)*s2, (-1j)*s3, (-1j)*s4, (-1j)*s5
def eta(tau, M):
    q=cmath.exp(2j*cmath.pi*tau)
    prod=1.0+0j
    for n in range(1, M+1): prod *= (1 - q**n)
    return q**(1.0/24.0) * prod
def C_series(x,tau,N):
    # derivatives at 0 with parity projection (theta1 odd)
    t0,t1,t2,t3,t4,t5 = _theta1_and_derivs5(0,tau,N)
    t0=0.0j; t2=0.0j; t4=0.0j
    fx0,fx1,fx2,fx3,fx4,fx5 = _theta1_and_derivs5(x,tau,N)
    # A(z)=theta1(x-z)=a0 + a1 z + a2 z^2/2 + a3 z^3/6 + a4 z^4/24
    a0=fx0; a1=-fx1; a2=fx2; a3=-fx3; a4=fx4
    # B(z)=theta1(-z)= b1 z + b2 z^2/2 + b3 z^3/6 + b4 z^4/24 + b5 z^5/120
    b1=-t1; b2=t2; b3=-t3; b4=t4; b5=-t5
    # Normalize A/a0 = 1 + A1 z + A2 z^2/2 + A3 z^3/6 + A4 z^4/24
    A1=a1/a0; A2=a2/a0; A3=a3/a0; A4=a4/a0
    # u(z)=B/(b1 z)=1 + alpha z + beta z^2 + gamma z^3 + delta z^4
    alpha = b2/(2*b1)
    beta  = b3/(6*b1)
    gamma = b4/(24*b1)
    delta = b5/(120*b1)
    # inverse series up to z^4
    inv0=1.0
    inv1=-alpha
    inv2=alpha*alpha - beta
    inv3=-(alpha**3) + 2*alpha*beta - gamma
    inv4=(alpha**4) - 3*(alpha**2)*beta + (beta**2) + 2*alpha*gamma - delta
    # S(z)=(A/a0)*(1/u) = 1 + s1 z + s2 z^2 + s3 z^3 + s4 z^4
    a2c=A2/2.0; a3c=A3/6.0; a4c=A4/24.0
    s1 = A1 + inv1
    s2 = a2c + A1*inv1 + inv2
    s3 = a3c + a2c*inv1 + A1*inv2 + inv3
    s4 = a4c + a3c*inv1 + a2c*inv2 + A1*inv3 + inv4
    # Raw C from regularized Phi: C_raw = -s4
    C_raw = -s4
    # Normalize by eta(tau)^3 (standard weak-Jacobi normalization)
    E = eta(tau, N)
    return C_raw / (E**3)
