# CY3 Elliptic Genus — Canonical Normal Form

**Statement.** For any Calabi–Yau threefold \(X\),
\[
\mathrm{Ell}_X(\tau,z)=\frac{\chi(X)}{2}\,\phi_{0,\frac{3}{2}}(\tau,z),
\qquad \chi(X)=\int_X c_3(TX).
\]
The unique weak Jacobi form \(\phi_{0,\frac{3}{2}}\) relates to our computational
building block \(C(\tau,z)\) by
\[
\phi_{0,\frac{3}{2}}(\tau,z)=\frac{1}{6}\,C(\tau,z),
\]
so \(\mathrm{Ell}_X=(\chi/12)\,C\).

**Holomorphy.** For unitary compact \((0,2)\) SCFTs the elliptic genus is holomorphic
in \((\tau,z)\) and transforms as a weak Jacobi form (weight 0, index \(m=c/6\)).
On a CY\(^3\) (\(c=18\Rightarrow m=3/2\)) any apparent \(z\)-poles in intermediate
\(\vartheta\)-ratios cancel across the three Chern roots; the finished invariant is poleless.
The observed Laurent symmetry in \(y=e^{2\pi i z}\) reflects this holomorphy.

**Cubic contraction (CY\(^3\)).**
With Chern roots \(x_i\) and
\[
\Phi(x;z,\tau)=\frac{\vartheta_1\!\big(\tfrac{x}{2\pi i}-z\big)}{\vartheta_1\!\big(\tfrac{x}{2\pi i}\big)}\,
\frac{\vartheta_1'(0)}{\vartheta_1(-z)},\qquad
C(z,\tau)=\frac{1}{6}\,\partial_x^3\Phi(0;z,\tau),
\]
the Witten-class expansion gives
\[
\prod_{i=1}^3\Phi(x_i;z,\tau)=1+C\,\sum_i x_i^3+\cdots.
\]
On a CY\(^3\), \(c_1=0\) and \(\sum_i x_i^3 = c_1^3-3c_1c_2+3c_3=3c_3\), hence
\[
\mathrm{Ell}_X(\tau,z)=3\,C(\tau,z)\!\int_X\!c_3 \;=\; \chi(X)\,\tfrac{C}{2}
\;=\;\frac{\chi(X)}{2}\,\phi_{0,\frac{3}{2}}.
\]

**Quintic specialization.** \(\chi(X)=-200\) so
\[
\mathrm{Ell}_X=-100\,\phi_{0,\frac{3}{2}}=-600\,\frac{C}{6}=-600\,C/6.
\]
The familiar “\(-600\)” is \(3\times\!\int_X c_3\), i.e. the cubic symmetric factor times Euler characteristic.

**What the code computes.** \(C\) via third \(x\)-derivative of \(\Phi\) at \(x=0\);
Fourier coefficients are extracted by two-\(\tau\) linear solves. Conditioning audit
(Branch `work/resume-20251005`) shows median \(1.842\times10^{-4}\), P90 \(4.220\times10^{-4}\).
Receipt Merkle (remote): see `tsv/elliptic_pass2_receipt.json`.
