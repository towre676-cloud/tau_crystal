import sys, cmath

def norm_cpx(s: str) -> complex:
    s = s.strip().replace('I','i')
    if 'j' not in s and 'J' not in s:
        s = s.replace('i','j')
    try:
        return complex(s)
    except Exception as e:
        raise SystemExit(f"[parse-error] cannot parse '{s}': {e}")

def jac_phi(z: complex, tau: complex, N: int):
    pi = cmath.pi; i = 1j
    q  = cmath.exp(2*pi*i*tau)
    y  = cmath.exp(2*pi*i*z)

    # Dedekind eta (q^(1/24) ∏(1-q^n))
    eta = q**(1/24)
    for n in range(1, N+1):
        eta *= (1 - q**n)

    # theta products (triple-product forms)
    # θ1
    theta1 = 2*(q**(1/8))*cmath.sin(pi*z)
    P = 1+0j
    for n in range(1, N+1):
        qn = q**n
        P *= (1 - qn)*(1 - y*qn)*(1 - (1/y)*qn)
    theta1 *= P

    # θ2
    theta2 = 2*(q**(1/8))*cmath.cos(pi*z)
    P = 1+0j
    for n in range(1, N+1):
        qn = q**n
        P *= (1 - qn)*(1 + y*qn)*(1 + (1/y)*qn)
    theta2 *= P

    # θ3
    P1 = 1+0j
    for n in range(1, N+1): P1 *= (1 - q**n)
    P2 = 1+0j
    for n in range(1, N+1):
        qh = q**(n-0.5); P2 *= (1 + y*qh)*(1 + (1/y)*qh)
    theta3 = P1*P2

    # θ4
    P1 = 1+0j
    for n in range(1, N+1): P1 *= (1 - q**n)
    P2 = 1+0j
    for n in range(1, N+1):
        qh = q**(n-0.5); P2 *= (1 - y*qh)*(1 - (1/y)*qh)
    theta4 = P1*P2

    # φ_{-2,1} = θ1^2 / η^6
    phi_m2_1 = (theta1*theta1)/(eta**6)

    # φ_{0,1} = 4*((θ2/θ2(0))^2 + (θ3/θ3(0))^2 + (θ4/θ4(0))^2)
    # Evaluate θi(0) via the same products at z=0
    # θ2(0)
    t2_0 = 2*(q**(1/8))
    P = 1+0j
    for n in range(1, N+1):
        qn = q**n; P *= (1 - qn)*(1 + qn)*(1 + qn)
    t2_0 *= P
    # θ3(0)
    P1 = 1+0j
    for n in range(1, N+1): P1 *= (1 - q**n)
    P2 = 1+0j
    for n in range(1, N+1):
        qh = q**(n-0.5); P2 *= (1 + qh)*(1 + qh)
    t3_0 = P1*P2
    # θ4(0)
    P1 = 1+0j
    for n in range(1, N+1): P1 *= (1 - q**n)
    P2 = 1+0j
    for n in range(1, N+1):
        qh = q**(n-0.5); P2 *= (1 - qh)*(1 - qh)
    t4_0 = P1*P2

    eps = 1e-30
    phi0_1 = 4*((theta2/(t2_0 if abs(t2_0)>eps else 1))**2
               + (theta3/(t3_0 if abs(t3_0)>eps else 1))**2
               + (theta4/(t4_0 if abs(t4_0)>eps else 1))**2)

    return phi_m2_1, phi0_1

if __name__ == "__main__":
    if len(sys.argv) < 4:
        raise SystemExit("usage: jac_phi.py z tau N")
    z   = norm_cpx(sys.argv[1])
    tau = norm_cpx(sys.argv[2])
    N   = int(sys.argv[3])
    pm2, p01 = jac_phi(z, tau, N)
    print(f"{pm2.real:.17e} {pm2.imag:.17e} {p01.real:.17e} {p01.imag:.17e}")
