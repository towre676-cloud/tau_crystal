import cmath, os, sys
sys.path.insert(0, os.path.dirname(__file__))
from ell_fourier import theta1_and_derivs
def phi_regularized(z, x, tau, N):
    # Φ(z) = (θ1(x-z)/θ1(x)) * θ1'(0)/θ1(-z)
    t0,t1,_,_ = theta1_and_derivs(0,tau,N)
    fx0,_,_,_ = theta1_and_derivs(x,tau,N)
    fz0,_,_,_ = theta1_and_derivs(x - z,tau,N)
    gz0,_,_,_ = theta1_and_derivs(-z,tau,N)
    B = fx0
    Phi = (fz0/B) * (t1/gz0)
    # Principal part near z=0 is -(θ1(x)/B)/z = -(1)/z. Remove it to get a regular value.
    return Phi + 1.0/z
def cubic_coeff_C(x, tau, N, h=1e-5):
    # Third derivative of the REGULARIZED Φ at 0 via symmetric 5-point stencil
    # Φ_reg'''(0) ≈ [-Φ_reg(2h) + 2Φ_reg(h) - 2Φ_reg(-h) + Φ_reg(-2h)] / h^3
    f2p = phi_regularized( 2*h, x, tau, N)
    f1p = phi_regularized(   h, x, tau, N)
    f1m = phi_regularized(  -h, x, tau, N)
    f2m = phi_regularized(-2*h, x, tau, N)
    d3 = (-f2p + 2*f1p - 2*f1m + f2m) / (h**3)
    # C = (1/6) Φ_reg'''(0)
    return d3/6.0
