import cmath
def q_from_tau(tau): return cmath.exp(2j*cmath.pi*tau)
def theta1_and_derivs(z,tau,N):
    q = q_from_tau(tau); twopi=2*cmath.pi
    s0=s1=s2=s3=0j
    for m in range(-N,N+1):
        n = m+0.5
        a = ((-1)**m) * q**(n*n) * cmath.exp(1j*twopi*n*z)
        f1 = 1j*twopi*n
        s0 += a
        s1 += a*f1
        s2 += a*(f1*f1)
        s3 += a*(f1*f1*f1)
    return (-1j)*s0, (-1j)*s1, (-1j)*s2, (-1j)*s3
def phi_third_at_zero(x,tau,N):
    # Phi(z) = theta1(x-z)/theta1(x) * theta1'(0)/theta1(-z)
    # Compute f = theta1(x - z), g = theta1(-z); need f(0..3), g(0..3) at z=0
    t0,t1,t2,t3 = theta1_and_derivs(0,tau,N)
    # theta1 is odd: t0≈0, t2≈0; keep numerics robust but do not rely solely on identities
    # f(z)=theta1(x-z): f0=θ1(x), f1=-θ1'(x), f2=θ1''(x), f3=-θ1'''(x)
    fx0,fx1,fx2,fx3 = theta1_and_derivs(x,tau,N)
    f0=fx0; f1=-fx1; f2=fx2; f3=-fx3
    # g(z)=theta1(-z): g0=θ1(0), g1=-θ1'(0), g2=θ1''(0), g3=-θ1'''(0)
    g0,g1p,g2p,g3p = t0,t1,t2,t3
    g1=-g1p; g2=g2p; g3=-g3p
    # constants
    B = fx0  # theta1(x)
    C = t1   # theta1'(0)
    # Φ = (C/B) * f/g ; compute third derivative at 0 using quotient/product rules
    # Define H(z)=f(z)/g(z). We need H'(0),H''(0),H'''(0).
    # Use series for f and g: f = f0 + f1 z + f2 z^2/2 + f3 z^3/6 + ... ; same for g.
    # Build via formal series inversion up to z^3 for g and multiply by f.
    # g(z) = g0 + g1 z + g2 z^2/2 + g3 z^3/6 ; compute inv series G(z)=1/g(z) to O(z^3).
    from math import factorial
    def s_eval(a0,a1,a2,a3,z):
        return a0 + a1*z + a2*(z*z)/2 + a3*(z*z*z)/6
    # Coefficients for g and its inverse around 0
    g0c, g1c, g2c, g3c = g0, g1, g2, g3
    if abs(g0c) < 1e-30:
        # Theta1(0)=0; we factor out the simple zero explicitly: g(z)=g1*z + g2*z^2/2 + ...
        # Write g(z)=z * u(z) with u(0)=g1. Then 1/g(z)= (1/z)*(1/u(z)).
        u0 = g1c
        u1 = g2c
        u2 = g3c
        # 1/u(z) series to O(z^2): v0=1/u0; v1= -u1/u0^2; v2=(2u1^2 - u0 u2)/u0^3
        v0 = 1.0/u0
        v1 = -u1/(u0*u0)
        v2 = (2*(u1*u1) - u0*u2)/(u0*u0*u0)
        # Thus G(z)=1/g(z) = (1/z)*(v0 + v1 z + v2 z^2/2)
        # f(z) series then multiplied by G(z) gives H(z)=f/g with pole terms canceling because f0=θ1(x) and C/B prefactor.
        # Build H coefficients up to z^2 in principal part and regularize the cubic.
        f0c,f1c,f2c,f3c = f0,f1,f2,f3
        # Multiply formal series carefully
        # H(z) = (f0c + f1c z + f2c z^2/2 + f3c z^3/6) * ( (v0/z) + v1 + v2 z/2 )  + O(z^2)
        # Collect coefficients up to z^2 terms after cancellation
        A_m1 = f0c*v0  # coefficient of z^-1 (should cancel after Φ prefactor)
        A0   = f0c*v1 + f1c*v0
        A1   = f0c*(v2/2) + f1c*v1 + (f2c/2)*v0
        A2   = f1c*(v2/2) + (f2c/2)*v1 + (f3c/6)*v0
        # Φ(z) = (C/B) * H(z). The physical integrand ensures the simple pole cancels; we enforce cancellation numerically by dropping A_{-1}.
        c_over_b = C/B
        phi0 = c_over_b*A0
        phi1 = c_over_b*A1
        phi2 = c_over_b*A2
        # Φ'''(0) = 6 * coeff(z^3), but with our truncated construction we approximate from lower terms; return None to signal regular path below.
        return None
    else:
        # generic safe branch (rarely hit for theta1 at 0); use quotient derivatives explicitly.
        f0c,f1c,f2c,f3c = f0,f1,f2,f3
        g0c,g1c,g2c,g3c = g0,g1,g2,g3
        # H'= (f' g - f g')/g^2 ; H'' and H''' obtained by differentiating (symbolically expanded below)
        H1 = (f1c*g0c - f0c*g1c)/(g0c*g0c)
        num2 = (f2c*g0c - f0c*g2c) - 2*(f1c*g1c - f0c*(g1c*g1c)/g0c)
        H2 = num2/(g0c*g0c)
        # For H3, use finite symbolic expansion via small h symmetry for robustness
        def H_of(z):
            fz0,fz1,fz2,fz3 = theta1_and_derivs(x-z,tau,N)
            gz0,gz1,gz2,gz3 = theta1_and_derivs(-z,tau,N)
            f = fz0; g = gz0
            return (C/B) * (f/g)
        h = 1e-6
        Hppp = ( -H_of(2*h) + 2*H_of(h) - 2*H_of(-h) + H_of(-2*h) )/(h*h*h)
        return Hppp
