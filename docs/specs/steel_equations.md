# Steel Equations: Hash‑Bound Formal Spec (Locked‑In)

_This file freezes the corrected specification. Scheme base is \( \\mathbb A^1_k\\setminus\\{0\\} \) over \( k=\\mathbb Q(b) \); the two‑loop derivative is corrected; all digests are domain‑separated._

### 1.  The affine RG leaf as a relative motive

Work over the tannakian base field \(k=\\mathbb Q(b)\). Regard the leaf as the pair \\(U,\\omega\\) with
\[
\boxed{\\;U=\\mathbb A^1_k\\setminus\\{0\\},\quad \\omega=\\frac{d\\mu}{\\mu^{2}}+b\,d\\ell\\;}
\]
satisfying the first integral
\[
I(\\mu,\\ell)=\\int\\omega=\\mu^{-1}+b\\ell=\\mu_0^{-1},\\qquad \\mu_0\\in\\mathbb Q_{>0}.
\]
De Rham realization with a marked class:
\[
\boxed{\\;\\mathsf M_{\\mathrm{dR}}=(H^1_{\\mathrm{dR}}(U/k),[\\omega])\\cong (k\cdot[\\mu^{-2}d\\mu],[\\mu^{-2}d\\mu+b\,d\\ell])\\;}
\]
Betti realization with a marked cycle \\([\\gamma]\\):
\[
\boxed{\\;\\mathsf M_{\\mathrm B}=(H_1(U(\\mathbb C),\\mathbb Z),[\\gamma])\\cong(\\mathbb Z\cdot[\\gamma],[\\gamma])\\;},\qquad \\mathrm{per}(\\omega)=\\int_{\\gamma}\\omega=\\mu_0^{-1}.
\]
Monodromy acts dimensionlessly on the first integral (deck transformations):
\[
\boxed{\\;T:\;I\\longmapsto I+2\\pi i\,n,\\quad n\\in\\mathbb Z\\;}
\]
The motive capsule serializes *marked* realizations and the comparison:
\[
\boxed{\\texttt{motive.json}=\\{\,k=\\mathbb Q(b),\,\\mu_0,\,[\\omega],\,[\\gamma],\,\\mathrm{per}(\\omega),\,T\,\\}}
\]
with domain‑separated digest
\[
\boxed{h_{\\mathsf M}=\\mathrm{Hash}_{256}(\\texttt{"MOTIVE"}\\parallel\\texttt{motive.json})}.
\]

### 2.  Whitening as an isometry of the motivic Gramian

Log‑sections \(s_i(\\ell)=\\log(m_i/m_0)\) obey \(ds_i/d\\ell=b(1-\\alpha_i)\). Use a normalized covariance over a declared compact interval \\([\\ell_-,\\ell_+]\\):
\[
\boxed{\\;\\Sigma_{ij}=\\frac{1}{\\ell_+-\\ell_-}\\int_{\\ell_-}^{\\ell_+}(s_i-\\bar s_i)(s_j-\\bar s_j)\,d\\ell,\quad \\bar s_i=\\frac{1}{\\ell_+-\\ell_-}\\int s_i\,d\\ell\\;}
\]
Whitening and equivariance:
\[
\boxed{\\;W=\\Sigma^{-1/2},\quad W^T\\Sigma W=I_5,\quad W\,P_w\\Sigma P_w^T W^T=O_w\in\\mathrm O(5),\; w\\in W(B_5)\\;}
\]
This canonically fixes the chamber \\(\\mathcal C\\).

### 3.  The chamber index as a rational point

For \(c\\in\\mathbb Q^5\):
\[
\boxed{\\;\\rho^{*}=Wc,\qquad r^{*}=\\Sigma^{-1}c\\;}
\]
Sort \\(|\\rho^{*}|\\) strictly to obtain \\(\\sigma\\). Ledger acceptance binds the *run*, not the motive hash:
\[
\boxed{\\;\\text{accept}\iff r^{*}\\in\\mathcal C\;\text{and}\; W\,P_w\\Sigma P_w^{T}W^{T}=O_w\;\\forall w\\in W(B_5)\\;}
\]
Metric‑invariant log‑Bayes with the \\(\\\\Sigma\\)‑unit ball \\(B_1(0)=\\{x: x^T\\Sigma x\\le 1\\}\\):
\[
\boxed{\\;\\log B=\\log\\frac{\\mathrm{Vol}(\\mathcal C\\cap B_1(0);\\Sigma)}{\\mathrm{Vol}(\\mathcal C_{\\mathrm{null}}\\cap B_1(0);\\Sigma_{\\mathrm{null}})}\\;}
\]

### 4.  Two‑loop deformation and exact perturbation (corrected derivative)

Primitive and Newton step:
\[
\boxed{\\;F(\\mu;\\ell)=\\ell+\\frac{1}{b\\mu}-\\frac{b_1}{b^{2}}\\log\\!\\Bigl(\\frac{b+b_1\\mu}{\\mu}\\Bigr)\\;},\qquad
\boxed{\\;F'(\\mu)= -\\frac{1}{b\\mu^{2}}-\\frac{b_{1}}{b^{2}}\\Bigl(\\frac{b_1}{b+b_1\\mu}-\\frac{1}{\\mu}\\Bigr)\\;}
\]
\[
\boxed{\\;\\mu_{n+1}=\\mu_n-\\frac{F(\\mu_n;\\ell)}{F'(\\mu_n;\\ell)}\\;}
\]
The symmetry contract persists at the level of construction, keeping \\(\\mathcal C\\) fixed; \\(\\Sigma(b_1)\\) remains in the same \\(\\mathrm O(5)\\)–orbit by design.

### 5.  Receipt grammar for exact symmetry

Run‑level receipt, separated from the motive capsule:
\[
\boxed{\\;\\texttt{receipt.json}=\\{h_{\\mathsf M},\,c,\,\\rho^{*},\,\\sigma,\,r^{*},\,\\log B,\,\\mathsf{eqv}=[W P_w\\Sigma P_w^T W^T=O_w]_{w},\,\\mathsf{in\\_C}=[r^{*}\\in\\mathcal C]\\}}
\]
Digest:
\[
\boxed{h_{\\mathrm{run}}=\\mathrm{Hash}_{256}(\\texttt{"RUN"}\\parallel\\texttt{receipt.json})}.
\]

### 6.  Cross‑place arithmetic via \(p\)‑adic periods

For \(p\\nmid \\mathrm{den}(\\mu_0)\\cdot\\mathrm{den}(b)\): Teichmüller lift \\(\\mu_0^{(p)}\\in\\mathbb Z_p^{\\times}\\), period and comparison
\[
\boxed{\\;\\mathrm{per}_{p}(\\omega)=(\\mu_0^{(p)})^{-1}\\in\\mathbb Z_p},\qquad \boxed{\\;\\iota_p(\\mathrm{per}(\\omega))\\equiv \\mathrm{per}_{p}(\\omega)\\ (\\mathrm{mod}\ p)\\;}
\]
Place‑tagged digest with declared precision \(N\):
\[
\boxed{h_{\\mathsf M}^{(p)}=\\mathrm{Hash}_{256}(\\texttt{"MOTIVE@p"}\\parallel p\\parallel \\mu_0^{(p)}\\parallel b\\parallel \\mathrm{per}_{p}(\\omega)\\parallel \\texttt{prec}=N)}.
\]

### 7.  Categorified index as a graded character

\[
\boxed{\\;C^{\\bullet}:\,0\\to C^0\\xrightarrow{d^0}C^1\\xrightarrow{d^1}C^2\\to 0,\; C^i\\simeq \\mathbb Q[B_5]^{\\oplus n_i},\; d^{i}\\in\\mathrm{Mat}_{n_{i+1}\\times n_i}(\\mathbb Q[B_5])\\;}
\]
Characters and verified identity for all \(g\\in B_5\):
\[
\chi_{B_5}(g)=\\sum_i(-1)^i\\,\\mathrm{Tr}_{C^i}(g),\qquad \\chi^{H}(g)=\\sum_i(-1)^i\\,\\mathrm{Tr}_{H^i}(C^{\\bullet})(g),\quad \boxed{\\chi_{B_5}(g)\\equiv \\chi^{H}(g)}.
\]

### 8.  Homotopical coherence as Kan filling

Histories as a simplicial set \(X_\\bullet\): \(X_0=\\{\\text{runs}\\}, X_1=\\{\\text{transport}\\}, X_2=\\{\\text{coherence}\\},\ldots\).
Selective Kan filling where contractually mandated; filler receipt:
\[
\boxed{\\;\\texttt{filler.json}=\\{n,k,\\;\\text{horn}=\\Lambda_k^n\\to X,\\;\\sigma\\in X_n,\\;\\partial_i\\sigma=\\text{faces},\\;\\mathrm{Hash}_{256}(\\sigma)\\}}
\]
Acceptance: \(\\text{accept}(\\texttt{horn})\\iff \\exists\\) filler in the specified degrees; otherwise record a red obstruction without mutating upstream hashes.

### 9.  Master Merkle root and locality of failure

Aggregate digests with domain separation into a Merkle root:
\[
\boxed{\\;\\mathbb H=(h_{\\mathsf M},\\{h_{\\mathsf M}^{(p)}\\}_p,\\;h_{\\mathrm{run}},\\;h_{\\mathrm{index}},\\;h_{\\mathrm{spec}},\\;h_{\\mathrm{homot}}),\quad H_\\tau=\\mathrm{Merkle}_{256}(\\mathbb H)\\;}
\]
Any mismatch invalidates \(H_\\tau\) and localizes the fault by the sibling path.
