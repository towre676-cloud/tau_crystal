from __future__ import annotations
import numpy as np
from typing import Tuple, Dict, Any, Optional

def _power_iter_lmax(A: np.ndarray, iters: int = 60, tol: float = 1e-10) -> float:
    n = A.shape[0]
    x = np.random.default_rng(42).standard_normal(n)
    x /= np.linalg.norm(x) + 1e-30
    lam = 0.0
    for _ in range(iters):
        y = A @ x
        ny = np.linalg.norm(y)
        if ny < tol: break
        x = y / ny
        lam_new = float(x @ (A @ x))
        if abs(lam_new - lam) < tol * (1.0 + abs(lam_new)):
            lam = lam_new; break
        lam = lam_new
    return max(lam, 0.0)

def _gersh_min(A: np.ndarray) -> float:
    # Gershgorin lower bound (often ~0 for Laplacians).
    n = A.shape[0]
    m = float('inf')
    for i in range(n):
        c = float(A[i,i])
        r = float(np.sum(np.abs(A[i,:])) - abs(c))
        m = min(m, c - r)
    return max(m, 0.0)

def _affine(A: np.ndarray, lmin: float, lmax: float) -> Tuple[np.ndarray, float, float]:
    if lmax <= lmin:
        return np.zeros_like(A), 0.0, 1.0
    alpha = (lmax + lmin)/2.0
    beta  = (lmax - lmin)/2.0
    return (A - alpha*np.eye(A.shape[0]))/beta, alpha, beta

def chebyshev_tau(A: np.ndarray, v: np.ndarray, k_max: int,
                  bounds: Optional[Tuple[float,float]] = None,
                  slope_window: int = 4, eps: float = 1e-12) -> Dict[str, Any]:
    n = A.shape[0]; assert v.shape[0] == n
    v0 = v.astype(float).copy()
    nrm = float(np.linalg.norm(v0) + eps)
    if nrm == 0.0: v0[0] = 1.0; nrm = 1.0
    v0 /= nrm
    if bounds is None:
        lmax = _power_iter_lmax(A)
        lmin = _gersh_min(A)
    else:
        lmin, lmax = bounds
    Atil, alpha, beta = _affine(A, lmin, lmax)
    rho = max(beta, eps)

    y0 = v0
    y1 = Atil @ v0
    E  = [float(y0 @ y0), float(y1 @ y1)]
    tau = [0.0, 0.0]

    y_prev, y_curr = y0, y1
    for _ in range(1, k_max):
        y_next = 2.0 * (Atil @ y_curr) - y_prev
        e = float(y_next @ y_next)
        E.append(e)
        i0 = max(0, len(E)-1-slope_window)
        logs = np.log(np.maximum(E[i0:], eps))
        slope = float(logs[-1] - logs[0])        # negative when energy drops
        d_tau = max(0.0, -slope) / rho
        tau.append(tau[-1] + d_tau)
        y_prev, y_curr = y_curr, y_next

    return {"E":E, "tau":tau, "alpha":float(alpha), "beta":float(beta),
            "lmin":float(lmin), "lmax":float(lmax), "v0_norm":nrm}
