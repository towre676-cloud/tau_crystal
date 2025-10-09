#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C

# placeholder self-test to prove the file runs
jacobi_selftest(){
  echo "[jacobi_core] OK"
}

# guard: run self-test if called directly
if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  jacobi_selftest
fi

# tiny python probe: prints exp(i*pi/3)
jacobi_python_probe(){
  python3 - <<'PY'
import cmath
z = cmath.exp(1j*cmath.pi/3)
print(f"[py] {z.real:.6f} {z.imag:.6f}")
PY
}

# jacobi_eval z tau N  -> prints: eta_r eta_i t1_r t1_i t2_r t2_i t3_r t3_i t4_r t4_i
jacobi_eval(){
# patched to accept i/j for complex inputs
  local z="$1"; local tau="$2"; local N="${3:-40}"
  python3 - "$z" "$tau" "$N" <<'PY'
import sys, cmath
z = complex(sys.argv[1]); tau = complex(sys.argv[2]); N = int(sys.argv[3])
pi = cmath.pi; i = 1j
q = cmath.exp(2*pi*i*tau)
y = cmath.exp(2*pi*i*z)

# Dedekind eta ~ q^(1/24) * prod_{n>=1} (1 - q^n)
eta = q**(1/24)
for n in range(1, N+1):
    eta *= (1 - q**n)

# theta1 via product: 2 q^(1/8) sin(pi z) prod (1 - q^n)(1 - y q^n)(1 - y^{-1} q^n)
theta1 = 2*(q**(1/8))*cmath.sin(pi*z)
prod = 1+0j
for n in range(1, N+1):
    qn = q**n
    prod *= (1 - qn)*(1 - y*qn)*(1 - (1/y)*qn)
theta1 *= prod

# theta2 via product: 2 q^(1/8) cos(pi z) prod (1 - q^n)(1 + y q^n)(1 + y^{-1} q^n)
theta2 = 2*(q**(1/8))*cmath.cos(pi*z)
prod = 1+0j
for n in range(1, N+1):
    qn = q**n
    prod *= (1 - qn)*(1 + y*qn)*(1 + (1/y)*qn)
theta2 *= prod

# theta3 via product: prod (1 - q^n) * prod (1 + y q^{n-1/2})(1 + y^{-1} q^{n-1/2})
theta3 = 1+0j
prodA = 1+0j
for n in range(1, N+1):
    prodA *= (1 - q**n)
prodB = 1+0j
for n in range(1, N+1):
    qh = q**(n-0.5)
    prodB *= (1 + y*qh)*(1 + (1/y)*qh)
theta3 = prodA*prodB

# theta4 via product: prod (1 - q^n) * prod (1 - y q^{n-1/2})(1 - y^{-1} q^{n-1/2})
theta4 = 1+0j
prodA = 1+0j
for n in range(1, N+1):
    prodA *= (1 - q**n)
prodB = 1+0j
for n in range(1, N+1):
    qh = q**(n-0.5)
    prodB *= (1 - y*qh)*(1 - (1/y)*qh)
theta4 = prodA*prodB

def pr(x): return f"{x.real:.17e} {x.imag:.17e}"
print(" ".join([pr(eta), pr(theta1), pr(theta2), pr(theta3), pr(theta4)]))
PY
}

# --- begin i/j normalization patch ---
_jacobi_norm_cplx(){
  # normalize a complex literal for Python: allow forms like 0.3+0.7i, 0.7i, 0.3-0.7i, or real
  local s="$1"
  s="${s//I/i}"
  # If it already has 'j' or 'J', keep; else convert trailing/embedded 'i' to 'j'
  if [[ "$s" != *"j"* && "$s" != *"J"* ]]; then
    s="${s//i/j}"
  fi
  printf '%s' "$s"
}
# override jacobi_eval to pre-normalize z, tau
jacobi_eval(){
  local z_raw="$1"; local tau_raw="$2"; local N="${3:-40}"
  local z="$(_jacobi_norm_cplx "$z_raw")"
  local tau="$(_jacobi_norm_cplx "$tau_raw")"
  python3 - "$z" "$tau" "$N" <<'PY'
import sys, cmath
def cpx(s):
    try:
        return complex(s)
    except Exception as e:
        raise SystemExit(f"[parse-error] cannot parse complex '{s}': {e}")
z = cpx(sys.argv[1]); tau = cpx(sys.argv[2]); N = int(sys.argv[3])
pi = cmath.pi; i = 1j
q = cmath.exp(2*pi*i*tau)
y = cmath.exp(2*pi*i*z)

eta = q**(1/24)
for n in range(1, N+1):
    eta *= (1 - q**n)

theta1 = 2*(q**(1/8))*cmath.sin(pi*z)
prod = 1+0j
for n in range(1, N+1):
    qn = q**n
    prod *= (1 - qn)*(1 - y*qn)*(1 - (1/y)*qn)
theta1 *= prod

theta2 = 2*(q**(1/8))*cmath.cos(pi*z)
prod = 1+0j
for n in range(1, N+1):
    qn = q**n
    prod *= (1 - qn)*(1 + y*qn)*(1 + (1/y)*qn)
theta2 *= prod

prodA = 1+0j
for n in range(1, N+1):
    prodA *= (1 - q**n)
prodB = 1+0j
for n in range(1, N+1):
    qh = q**(n-0.5)
    prodB *= (1 + y*qh)*(1 + (1/y)*qh)
theta3 = prodA*prodB

prodA = 1+0j
for n in range(1, N+1):
    prodA *= (1 - q**n)
prodB = 1+0j
for n in range(1, N+1):
    qh = q**(n-0.5)
    prodB *= (1 - y*qh)*(1 - (1/y)*qh)
theta4 = prodA*prodB

def pr(x): return f"{x.real:.17e} {x.imag:.17e}"
print(" ".join([pr(eta), pr(theta1), pr(theta2), pr(theta3), pr(theta4)]))
PY
}
# --- end patch ---

# --- robust jacobi_phi: pure-Python, no process substitution ---
jacobi_phi(){
  # accepts z,tau using i or j (e.g. 0.3+0.7i)
  local _norm(){ local s="$1"; s="${s//I/i}"; [[ "$s" == *j* || "$s" == *J* ]] || s="${s//i/j}"; printf '%s' "$s"; }
  local z="$(_norm "${1:?z}")"; local tau="$(_norm "${2:?tau}")"; local N="${3:-40}"
  python3 - "$z" "$tau" "$N" <<'PY'
import sys, cmath
def cpx(s):
    try: return complex(s)
    except Exception as e: raise SystemExit(f"[parse-error] {s}: {e}")
z = cpx(sys.argv[1]); tau = cpx(sys.argv[2]); N = int(sys.argv[3])
pi=cmath.pi; i=1j
q=cmath.exp(2*pi*i*tau); y=cmath.exp(2*pi*i*z)

# Dedekind eta
eta=q**(1/24)
for n in range(1,N+1): eta *= (1 - q**n)

# theta products (Jacobi triple product forms)
def theta(kind, z, y):
    if kind==1:
        val=2*(q**(1/8))*cmath.sin(pi*z); P=1+0j
        for n in range(1,N+1):
            qn=q**n; P*= (1 - qn)*(1 - y*qn)*(1 - (1/y)*qn)
        return val*P
    if kind==2:
        val=2*(q**(1/8))*cmath.cos(pi*z); P=1+0j
        for n in range(1,N+1):
            qn=q**n; P*= (1 - qn)*(1 + y*qn)*(1 + (1/y)*qn)
        return val*P
    if kind==3:
        P1=1+0j
        for n in range(1,N+1): P1*= (1 - q**n)
        P2=1+0j
        for n in range(1,N+1):
            qh=q**(n-0.5); P2*= (1 + y*qh)*(1 + (1/y)*qh)
        return P1*P2
    if kind==4:
        P1=1+0j
        for n in range(1,N+1): P1*= (1 - q**n)
        P2=1+0j
        for n in range(1,N+1):
            qh=q**(n-0.5); P2*= (1 - y*qh)*(1 - (1/y)*qh)
        return P1*P2
    raise ValueError
t1=theta(1,z,y); t2=theta(2,z,y); t3=theta(3,z,y); t4=theta(4,z,y)

# φ_{-2,1} = θ1^2 / η^6
phi_m2_1 = (t1*t1)/(eta**6)

# φ_{0,1} = 4*((θ2/θ2(0))^2+(θ3/θ3(0))^2+(θ4/θ4(0))^2) using product evals at z=0
def theta0(kind):
    if kind==2:
        val=2*(q**(1/8)); P=1+0j
        for n in range(1,N+1):
            qn=q**n; P*= (1 - qn)*(1 + qn)*(1 + qn)
        return val*P
    if kind==3:
        P1=1+0j
        for n in range(1,N+1): P1*= (1 - q**n)
        P2=1+0j
        for n in range(1,N+1):
            qh=q**(n-0.5); P2*= (1 + qh)*(1 + qh)
        return P1*P2
    if kind==4:
        P1=1+0j
        for n in range(1,N+1): P1*= (1 - q**n)
        P2=1+0j
        for n in range(1,N+1):
            qh=q**(n-0.5); P2*= (1 - qh)*(1 - qh)
        return P1*P2
t20, t30, t40 = theta0(2), theta0(3), theta0(4)
eps=1e-30
phi0_1 = 4*((t2/(t20 if abs(t20)>eps else 1))**2
            + (t3/(t30 if abs(t30)>eps else 1))**2
            + (t4/(t40 if abs(t40)>eps else 1))**2)

print(f"{phi_m2_1.real:.17e} {phi_m2_1.imag:.17e} {phi0_1.real:.17e} {phi0_1.imag:.17e}")
PY
}
# --- end robust jacobi_phi ---

# root-aware, robust φ-evaluator (uses scripts/ell/jac_phi.py)
jacobi_phi2(){
  local ROOT="${ROOT_OVERRIDE:-$HOME/Desktop/tau_crystal/tau_crystal}"
  cd "$ROOT" || { echo "[err] cannot cd to $ROOT"; return 2; }
  local z="$1"; local tau="$2"; local N="${3:-40}"
  # normalize i->j for Python
  z="${z//I/i}"; [[ "$z" == *j* || "$z" == *J* ]] || z="${z//i/j}"
  tau="${tau//I/i}"; [[ "$tau" == *j* || "$tau" == *J* ]] || tau="${tau//i/j}"
  if command -v python3 >/dev/null 2>&1; then
    python3 scripts/ell/jac_phi.py "$z" "$tau" "$N"
  else
    python scripts/ell/jac_phi.py "$z" "$tau" "$N"
  fi
}

