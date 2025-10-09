import sys, cmath, math, itertools, pathlib, json, os

def norm_tau(s: str) -> complex:
    s = s.strip().replace('I','i')
    if 'j' not in s and 'J' not in s:
        s = s.replace('i','j')
    return complex(s)

def main():
    if len(sys.argv) < 4:
        print("usage: make_quintic_grid.py y tau_list_json N", file=sys.stderr)
        sys.exit(2)
    y   = float(sys.argv[1])
    taus= json.loads(sys.argv[2])   # e.g. ["0.2+0.6j","0.3+0.7j","0.4+0.8j"]
    N   = int(sys.argv[3])

    # z from y = exp(2π i z): choose the principal branch
    z = cmath.log(y) / (2j*cmath.pi)

    root = pathlib.Path(os.environ.get("ROOT_OVERRIDE", "")) or pathlib.Path.home() / "Desktop" / "tau_crystal" / "tau_crystal"
    worker = root / "scripts" / "ell" / "jac_phi.py"
    outp   = root / "tmp" / "ell_quintic_grid.tsv"
    outp.parent.mkdir(parents=True, exist_ok=True)

    # header
    lines = ["#Re(tau)\tIm(tau)\tRe(z)\tIm(z)\tphi_m2_1_r\tphi_m2_1_i\tphi0_1_r\tphi0_1_i"]

    # compute φ’s by importing the worker once (faster & safer than subprocess)
    sys.path.insert(0, str((root / "scripts" / "ell").resolve()))
    import jac_phi as W

    for t in taus:
        tau = norm_tau(t)
        pm2, p01 = W.jac_phi(z, tau, N)
        lines.append(f"{tau.real:.9f}\t{tau.imag:.9f}\t{z.real:.9e}\t{z.imag:.9e}\t"
                     f"{pm2.real:.9e}\t{pm2.imag:.9e}\t{p01.real:.9e}\t{p01.imag:.9e}")

    outp.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[grid] wrote {outp}")
    # also print a peek
    for L in lines[:5]:
        print(L)

if __name__ == "__main__":
    main()
