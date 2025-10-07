# Universal Normal Form (CY3, ASCII)

Claim. For any Calabi–Yau threefold X (c1(TX)=0),
  Ell_X(q,y) = (chi(X)/2) * phi_{0,3/2}(q,y)
where phi_{0,3/2} is the universal weak Jacobi form (weight 0, index 3/2).

Quintic. chi = -200  =>  Ell_Quintic = -100 * phi_{0,3/2}.

Cubic factor (geometry). With c1=0, linear/quadratic symmetric polynomials vanish;
the cubic symmetric polynomial equals 3*c3(TX). Our theta-product channel contracts
against sum x_i^3, so the factor 3 appears automatically. In code units:
  C(z;τ) := (1/6) * d^3/dz^3 Phi |_{z=0},  and  phi_{0,3/2} = C/6,
hence the apparent -600 = 6 * (-100): (six from cubic derivative) * (chi/2).

Holomorphy. Pole cancellation across the three Chern roots yields a holomorphic
weak Jacobi form. Numerically: stable charge-conjugation symmetry; no blowups.
