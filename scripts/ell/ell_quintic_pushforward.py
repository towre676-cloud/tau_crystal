## [CY3 Normal Form]
## Ell_X(q,y) = (chi(X)/2) * phi_{0,3/2}(q,y)   (weight 0, index 3/2)
## Quintic: chi = -200 -> Ell = -100 * phi_{0,3/2}
## Dictionary:
##   C := (1/6) * d^3/dz^3 Phi |_{z=0},   phi_{0,3/2} = C/6
##   cubic factor = geometric: with c1=0, cubic symmetric polynomial = 3*c3(TX)
## Holomorphy: theta-ratio poles cancel over three Chern roots (CY3), giving a holomorphic weak Jacobi form.
import sys, cmath, math

# Accept "i" or "j" in complex literals
def norm_cpx(s: str) -> complex:
    s = s.strip().replace('I','i')
    if 'j' not in s and 'J' not in s:
        s = s.replace('i','j')
    try:
        return complex(s)
    except Exception as e:
        raise SystemExit(f"[parse-error] cannot parse '{s}': {e}")

def eta_tau(tau: complex, N: int) -> complex:
    q = cmath.exp(2j*cmath.pi*tau)
    e = q**(1/24)
    for n in range(1, N+1):
        e *= (1 - q**n)
    return e

def theta1_prod(u: complex, q: complex, N: int) -> complex:
    # θ1(u|τ) = 2 q^(1/8) sin(πu) ∏_{n>=1} (1 - q^n)(1 - y q^n)(1 - y^{-1} q^n), y=e^{2πiu}
    y = cmath.exp(2j*cmath.pi*u)
    val = 2*(q**(1/8))*cmath.sin(cmath.pi*u)
    P = 1+0j
    for n in range(1, N+1):
        qn = q**n
        P *= (1 - qn)*(1 - y*qn)*(1 - (1/y)*qn)
    return val*P

def theta1(u: complex, tau: complex, N: int) -> complex:
    q = cmath.exp(2j*cmath.pi*tau)
    return theta1_prod(u, q, N)

def theta1p0(tau: complex, N: int) -> complex:
    # θ1'(0|τ) = 2π η(τ)^3
    e = eta_tau(tau, N)
    return 2*cmath.pi*(e**3)

def phi_norm(x: complex, z: complex, tau: complex, N: int) -> complex:
    # Φ(x) = [θ1(x/(2πi)-z)/θ1(x/(2πi))] * [θ1'(0)/θ1(-z)], with Φ(0)=1
    u = x/(2j*cmath.pi)
    num = theta1(u - z, tau, N)
    den = theta1(u,       tau, N)
    cst = theta1p0(tau, N)/theta1(-z, tau, N)
    return (num/den)*cst

def cubic_coeff_C(z: complex, tau: complex, N: int, h: float=1e-6) -> complex:
    # Complex-step 3rd derivative at 0 for Φ: Φ'''(0) from Φ(ih), Φ(2ih), Φ(3ih)
    i = 1j
    f0 = 1.0 + 0j
    f1 = phi_norm(1.0*i*h, z, tau, N)
    f2 = phi_norm(2.0*i*h, z, tau, N)
    f3 = phi_norm(3.0*i*h, z, tau, N)
    # Third-derivative finite difference that cancels lower orders:
    # num = ( -11 Φ(0) + 18 Φ(ih) - 9 Φ(2ih) + 2 Φ(3ih) ) / 6
    num = (-11*f0 + 18*f1 - 9*f2 + 2*f3)/6.0
    d3  = num / ((i**3)*(h**3))  # Φ'''(0)
    C   = d3/6.0
    return C

def main():
    if len(sys.argv) < 4:
        print("usage: ell_quintic_pushforward.py z tau N", file=sys.stderr)
        sys.exit(2)
    z   = norm_cpx(sys.argv[1])
    tau = norm_cpx(sys.argv[2])
    N   = int(sys.argv[3])
    C = cubic_coeff_C(z, tau, N)
    # For a CY3 quintic: Ell(X) = -600 * C  (since ∫ c3 = -200, and Σ x_i^3 = 3 c3)
    ell = -600.0 * C
    print(f"{ell.real:.17e} {ell.imag:.17e}")

if __name__ == "__main__":
    main()
