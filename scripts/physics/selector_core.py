#!/usr/bin/env python3
import math

def k_min_from_error(A, sigma, eps_max):
    if A <= 0 or sigma <= 0 or eps_max <= 0:
        return 0
    return max(0, math.ceil(-math.log(eps_max / A) / sigma))

def n_caps(k, budgets, coeffs, io_frac=0.0, beta=2.0e9):
    L_max, M_max, M0 = budgets["L_max"], budgets["M_max"], budgets["M0"]
    w1, w2 = coeffs["W"]["w1"], coeffs["W"]["w2"]
    s0, s1, s2 = coeffs["S"]["s0"], coeffs["S"]["s1"], coeffs["S"]["s2"]
    c_time     = coeffs["c_time"]

    caps = []

    # compute-time
    d = c_time * (w1 + w2*k)
    if d > 0:
        caps.append(L_max / d)

    # memory
    d = (s1 + s2*k)
    num = (M_max - M0 - s0)
    if d > 0 and num > 0:
        caps.append(num / d)

    # I/O
    if io_frac and io_frac > 0:
        d = io_frac * (s1 + s2*k)
        num = (beta * L_max - io_frac * s0)
        if d > 0 and num > 0:
            caps.append(num / d)

    return math.floor(min(caps)) if caps else 0

def select_feasible(budgets, coeffs, error_model, io_frac=0.0, beta=2.0e9,
                    objective="max_k_then_n", k_pad=4096):
    A = error_model.get("A", 1.0)
    sigma = error_model.get("sigma", 1.0)
    km = k_min_from_error(A, sigma, budgets["eps_max"])

    # crude k upper bounds requiring n>=1
    k_maxs = []
    w1, w2 = coeffs["W"]["w1"], coeffs["W"]["w2"]
    s0, s1, s2 = coeffs["S"]["s0"], coeffs["S"]["s1"], coeffs["S"]["s2"]
    ct, L_max, M_max, M0 = coeffs["c_time"], budgets["L_max"], budgets["M_max"], budgets["M0"]

    if w2 > 0:
        k_maxs.append(math.floor((L_max/ct - w1) / w2))
    if s2 > 0 and (M_max - M0 - s0 - s1) > 0:
        k_maxs.append(math.floor((M_max - M0 - s0 - s1) / s2))

    kM = max(km, 0)
    kX = max(km, min(k_maxs) if k_maxs else km + k_pad)

    best = None
    for k in range(kM, max(kM, kX) + 1):
        ncap = n_caps(k, budgets, coeffs, io_frac, beta)
        if ncap < 1:
            continue
        n = ncap  # choose largest n by default
        cand = {"n": n, "k": k, "ncap": ncap}
        if best is None:
            best = cand
            continue
        if objective == "max_k_then_n":
            best = max([best, cand], key=lambda c: (c["k"], c["n"]))
        elif objective == "min_n_plus_k":
            best = min([best, cand], key=lambda c: (c["n"] + c["k"], c["n"]))
        else:
            best = cand
    return best
