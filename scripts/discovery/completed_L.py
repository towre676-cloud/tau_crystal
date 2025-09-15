import mpmath as mp

# Γ_R(s) = π^{-s/2} Γ(s/2),  Γ_C(s) = (2π)^{-s} Γ(s)
def Gamma_R(s): return mp.pi**(-s/2)*mp.gamma(s/2)
def Gamma_C(s): return (2*mp.pi)**(-s)*mp.gamma(s)

def complete_L(s, Lfunc, Q: float, gamma_type="R", epsilon=1, shift=0.0):
    """Λ(s) = Q^{s/2} * Γ_* (s+shift) * L(s), with simple gamma_type switch."""
    if gamma_type.upper() == "C":
        G = Gamma_C(s + shift)
    else:
        G = Gamma_R(s + shift)
    return (Q**(s/2))*G*Lfunc(s) * (1 if epsilon in (None,"",0) else 1)
