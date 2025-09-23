# Primitive Hybrid Corridor (Abelian)

This corridor checks two conditions for tuples (n,g,h,k_claim,factors):
1) LOCAL_OK: fast congruence witness g^k ≡ h (mod n) with gcd(g,n)=1.
2) ARK_BALANCED: archimedean log balance |log|h|| ≈ k·log|g|| within ε.
If both hold, the corridor declares GLOBAL_OK and emits a receipt with a hash.
