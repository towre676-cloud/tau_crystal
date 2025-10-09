import sys, json, cmath, pathlib, os

def norm_tau(s: str) -> complex:
    s = s.strip().replace('I','i')
    if 'j' not in s and 'J' not in s:
        s = s.replace('i','j')
    return complex(s)

def norm_cpx(s: str) -> complex:
    return norm_tau(s)

# Copy the worker methods directly to avoid imports
def eta_tau(tau: complex, N: int) -> complex:
    q = cmath.exp(2j*cmath.pi*tau)
    e = q**(1/24)
    for n in range(1, N+1):
        e *= (1 - q**n)
    return e

def theta1_prod(u: complex, q: complex, N: int) -> complex:
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
    e = eta_tau(tau, N)
    return 2*cmath.pi*(e**3)

def phi_norm(x: complex, z: complex, tau: complex, N: int) -> complex:
    u = x/(2j*cmath.pi)
    num = theta1(u - z, tau, N)
    den = theta1(u,       tau, N)
    cst = theta1p0(tau, N)/theta1(-z, tau, N)
    return (num/den)*cst

def cubic_coeff_C(z: complex, tau: complex, N: int, h: float=1e-6) -> complex:
    i = 1j
    f0 = 1.0 + 0j
    f1 = phi_norm(1.0*i*h, z, tau, N)
    f2 = phi_norm(2.0*i*h, z, tau, N)
    f3 = phi_norm(3.0*i*h, z, tau, N)
    num = (-11*f0 + 18*f1 - 9*f2 + 2*f3)/6.0
    d3  = num / ((i**3)*(h**3))
    return d3/6.0

def main():
    if len(sys.argv) < 4:
        print("usage: make_quintic_push_table.py y tau_list_json N", file=sys.stderr)
        sys.exit(2)
    y    = float(sys.argv[1])
    taus = json.loads(sys.argv[2])  # e.g. ["0.2+0.6j","0.3+0.7j","0.4+0.8j"]
    N    = int(sys.argv[3])

    # z from y = exp(2π i z), principal branch
    z = cmath.log(y) / (2j*cmath.pi)

    root = pathlib.Path(os.environ.get("ROOT_OVERRIDE", "")) or pathlib.Path.home()/ "Desktop" / "tau_crystal" / "tau_crystal"
    outp = root / "tmp" / "ell_quintic_push.tsv"
    outp.parent.mkdir(parents=True, exist_ok=True)

    rows = ["#Re(tau)\tIm(tau)\tRe(z)\tIm(z)\tEll_r\tEll_i"]
    for t in taus:
        tau = norm_tau(t)
        C = cubic_coeff_C(z, tau, N)
        ell = -600.0*C
        rows.append(f"{tau.real:.9f}\t{tau.imag:.9f}\t{z.real:.9e}\t{z.imag:.9e}\t{ell.real:.9e}\t{ell.imag:.9e}")

    outp.write_text("\n".join(rows) + "\n", encoding="utf-8")
    print(f"[push] wrote {outp}")
    for L in rows[:5]:
        print(L)

if __name__ == "__main__":
    main()
