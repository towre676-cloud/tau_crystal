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

### 10.  The \(B_{5}\)–anomaly as an invertible TQFT, with receipts

Fix a spacetime dimension \(d\ge 0\) and let \(\mathrm{Bord}^{B_{5}}_{d}\) denote the symmetric monoidal \(d\)–dimensional bordism category of closed \(d\)–manifolds \(M\) equipped with a principal \(B_{5}\)–bundle \(P\to M\) (classifying map \(f:M\to \mathrm{B}B_{5}\)), monoidal product given by disjoint union. An anomaly is an invertible, symmetric-monoidal functor
\[
\boxed{\quad Z_{\mathrm{anom}}:\ \mathrm{Bord}^{B_{5}}_{d}\longrightarrow \mathrm{Lines}^{\times}\quad}
\]
to the Picard groupoid of one-dimensional complex lines, with values obeying locality and gluing. Freed–Hopkins classify such theories by stable maps
\[
\boxed{\quad[\ \mathrm{MTH}\wedge (\mathrm{B}B_{5})_{+}\ ,\ \Sigma^{d+1}I\mathbb Z\ ]\quad}
\]
where \(\mathrm{MTH}\) is the Thom spectrum for the chosen tangential structure \(H\) (e.g. \(\mathrm{SO}\), \(\mathrm{Spin}\)), \(I\mathbb Z\) is the Anderson dual of the sphere, and \(\Sigma^{d+1}\) denotes \((d{+}1)\)–fold suspension. Choosing a representative \(\Phi\) in this homotopy class and a differential refinement \(\widehat \Phi\) determines the partition function on a closed, \(B_{5}\)–decorated \(d\)–manifold \((M,f)\) by evaluation on the corresponding bordism class:
\[
\boxed{\quad Z_{\mathrm{anom}}(M,f)\;=\;\exp\!\Bigl(2\pi i\ \langle \Phi,\ [M,f]\rangle\Bigr)\ \in U(1).\quad}
\]

When \(\Phi\) admits a differential cocycle representative \(\widehat{\alpha}\) (e.g. in group cohomology \(H^{d+1}(\mathrm{B}B_{5},\mathbb Z)\) for bosonic internal symmetry), one may compute by bulk–boundary splitting. For a compact \((d{+}1)\)–manifold \(X\) with \(\partial X=M\) and an extension \(F:X\to \mathrm{B}B_{5}\) of \(f\),
\[
\boxed{\quad \log Z_{\mathrm{anom}}(M,f)\;=\;2\pi i\!\int_{X} \mathrm{CS}_{d+1}(F,R)\;-\;\pi i\,\frac{\eta(D_{\partial})+h}{2}\quad}
\]
where \(\mathrm{CS}_{d+1}(F,R)\) is a Chern–Simons–type transgression refining \(\widehat{\alpha}\) (depending on the \(B_{5}\)–bundle and, if present, curvature \(R\) of the tangential structure), and \(\eta(D_{\partial})\) is the Atiyah–Patodi–Singer \(\eta\)–invariant with \(h\) its kernel dimension. The right-hand side is independent of the chosen filling \(X\) (mod \(\mathbb Z\)) exactly when the bulk class is integral; this is the anomaly well-definedness condition.

Locality and gluing, written multiplicatively in \(U(1)\). For disjoint union,
\[
\boxed{\quad Z_{\mathrm{anom}}(M_1\sqcup M_2,f_1\sqcup f_2)\ =\ Z_{\mathrm{anom}}(M_1,f_1)\,\cdot\,Z_{\mathrm{anom}}(M_2,f_2)\quad}
\]
and for a glued bordism \(X=X_1\cup_{(Y,g)} X_2\) along a common \(B_{5}\)–decorated boundary \((Y,g)\),
\[
\boxed{\quad Z_{\mathrm{anom}}(\partial X,g|_{\partial X})\ =\ \big\langle\,Z_{\mathrm{anom}}(\partial X_1,g|_{\partial X_1})\ ,\ Z_{\mathrm{anom}}(\partial X_2,g|_{\partial X_2})\,\big\rangle_{(Y,g)}\quad}
\]
where \(\langle\cdot,\cdot\rangle_{(Y,g)}\) is the canonical pairing of lines assigned to \((Y,g)\) and its orientation-reversal. Gauge invariance under \(B_{5}\) is the statement that for any bundle isomorphism \(f\simeq f^{\gamma}\) induced by \(\gamma:M\to B_{5}\),
\[
\boxed{\quad Z_{\mathrm{anom}}(M,f^{\gamma})\;=\;Z_{\mathrm{anom}}(M,f).\quad}
\]

To couple this anomaly to the \(\tau\)-Crystal corridor, designate a canonical test object \((M_{\star},f_{\star})\) built from the chamber data. Write \(w\in W(B_{5})\) for the signed-permutation symmetry fixed by whitening, and let \(f_{\rho}:M_{\star}\to \mathrm{B}B_{5}\) classify the holonomy determined by the chamber index \(\sigma\) and signs of \(r^{*}\). Define the normalization of the statistical observable \(\log B\) by
\[
\boxed{\quad e^{\,\log B}\ :=\ Z_{\mathrm{anom}}(M_{\star},f_{\rho}),\qquad \text{so that }\ \log B\equiv \log Z_{\mathrm{anom}}(M_{\star},f_{\rho})\ (\mathrm{mod}\ 2\pi i).\quad}
\]
With this identification, every symmetry or locality statement about \(\log B\) becomes a corresponding TQFT identity, hence testable by the anomaly receipts.

#### Anomaly receipts and the ledger contract

The cocycle capsule records the classification data:
\[
\boxed{\ \texttt{anom\_class.json}\ =\ \bigl\{\ d,\ H,\ \Phi,\ \widehat{\alpha},\ \texttt{model}=\texttt{\"cohomology\"}\ \text{or}\ \texttt{\"eta+CS\"}\ \bigr\},\quad
h_{\mathrm{class}}=\mathrm{Hash}_{256}\bigl(\texttt{\"ANOM\_CLASS\"}\parallel \texttt{anom\_class.json}\bigr).\ }
\]

A single manifold evaluation records the geometry and the result:
\[
\boxed{\ \texttt{anom\_eval.json}\ =\ \bigl\{\ d,\ M,\ \texttt{triangulation/cell\_data},\ f,\ \texttt{cochain\_pullback},\ Z=\exp(2\pi i\,S),\ S\in \mathbb R/\mathbb Z,\ \texttt{bulk}=\texttt{APS/CS\ split\ (optional)}\ \bigr\},}
\]
\[
\boxed{\ h_{\mathrm{eval}}=\mathrm{Hash}_{256}\bigl(\texttt{\"ANOM\_EVAL\"}\parallel h_{\mathrm{class}}\parallel \texttt{anom\_eval.json}\bigr).}
\]

Disjoint union constraint:
\[
\boxed{\ \texttt{anom\_tensor.json}\ =\ \bigl\{\ (M_1,f_1),(M_2,f_2),(M,f),\ Z_1,\ Z_2,\ Z,\ \texttt{ok}=[Z\overset{?}{=}Z_1Z_2]\ \bigr\},\quad
h_{\otimes}=\mathrm{Hash}_{256}\bigl(\texttt{\"ANOM\_TENSOR\"}\parallel \texttt{anom\_tensor.json}\bigr).}
\]
Gluing constraint along \((Y,g)\):
\[
\boxed{\ \texttt{anom\_glue.json}\ =\ \bigl\{\ X_1,\ X_2,\ Y,\ Z_{\partial X_1},\ Z_{\partial X_2},\ Z_{\partial X},\ \texttt{ok}=[Z_{\partial X}\overset{?}{=}\langle Z_{\partial X_1},Z_{\partial X_2}\rangle_Y]\ \bigr\},}
\]
\[
\boxed{\ h_{\mathrm{glue}}=\mathrm{Hash}_{256}\bigl(\texttt{\"ANOM\_GLUE\"}\parallel \texttt{anom\_glue.json}\bigr).}
\]

Aggregate anomaly digest via a Merkle root to preserve locality of failure:
\[
\boxed{\ h_{\mathrm{anom}}=\mathrm{Merkle}_{256}\Bigl(\,h_{\mathrm{class}},\ \{h_{\mathrm{eval}}\},\ \{h_{\otimes}\},\ \{h_{\mathrm{glue}}\}\Bigr).}
\]

#### Differential and group-cohomology calculators

**Cohomology model.** Choose a cellular model for \(M\) with a simplicial map \(f:M\to \mathrm{B}B_{5}\). Fix a normalized \((d{+}1)\)–cocycle \(c_{d+1}\) representing \(\alpha\in H^{d+1}(\mathrm{B}B_{5},\mathbb Z)\). Pull back to \(f^{*}c_{d+1}\) and evaluate
\[
\boxed{\quad Z_{\mathrm{anom}}(M,f)=\exp\!\Bigl(2\pi i\ \langle f^{*}c_{d+1},\ [M]\rangle\Bigr).\quad}
\]
Include the explicit cochain on each \((d{+}1)\)–cell in the receipt so replay does not require recomputation.

**\(\eta\)+CS model.** Choose a filling \(X\) and compute
\[
\boxed{\quad \log Z_{\mathrm{anom}}(M,f)=2\pi i \int_{X}\mathrm{CS}_{d+1}(F,R)\ -\ \pi i\frac{\eta+h}{2}\quad}
\]
together with a second filling \(X'\) to certify independence mod \(\mathbb Z\) by comparing \(X\cup_M \overline{X'}\).

#### Coupling to \(\log B\) and exact symmetry

Fix \((M_{\star},f_{\rho})\) from the chamber \(\mathcal C\) and whitening’s \(W(B_{5})\) action. Declare
\[
\boxed{\quad e^{\,\log B}\ :=\ Z_{\mathrm{anom}}(M_{\star},f_{\rho})\quad}
\]
and serialize the coupling
\[
\boxed{\ \texttt{anom\_couple.json}=\{\ h_{\mathrm{anom}},\ h_{\mathrm{run}},\ (M_{\star},f_{\rho}),\ \log B,\ \texttt{ok}=[\,e^{\log B}\overset{?}{=}Z_{\mathrm{anom}}(M_{\star},f_{\rho})\,]\ \},}
\]
\[
\boxed{\ h_{\mathrm{couple}}=\mathrm{Hash}_{256}\bigl(\texttt{\"ANOM\_COUPLE\"}\parallel \texttt{anom\_couple.json}\bigr).}
\]
Exact \(B_{5}\) symmetry is enforced on statistics by the whitening-equivariance receipts and on topology by gauge invariance \(Z_{\mathrm{anom}}(M_{\star},f_{\rho}^{\gamma})=Z_{\mathrm{anom}}(M_{\star},f_{\rho})\) for any \(\gamma:M_{\star}\to B_{5}\).

#### Acceptance predicate and master binding

The ledger accepts the anomaly run precisely when every recorded \(\texttt{ok}\) flag in \(\texttt{anom\_tensor.json}\), \(\texttt{anom\_glue.json}\), and \(\texttt{anom\_couple.json}\) is true and the two-filling checks agree modulo \(\mathbb Z\). The anomaly digest then enters the corridor root
\[
\boxed{\quad H_{\tau}=\mathrm{Merkle}_{256}\Bigl(\,h_{\mathsf M},\ \{h_{\mathsf M}^{(p)}\},\ h_{\mathrm{run}},\ h_{\mathrm{index}},\ h_{\mathrm{spec}},\ h_{\mathrm{homot}},\ h_{\mathrm{anom}}\Bigr)\quad}
\]
so any failure in locality, gluing, gauge invariance, or coupling to \(\log B\) breaks \(H_{\tau}\) and isolates the offending leaf via its Merkle sibling path.

