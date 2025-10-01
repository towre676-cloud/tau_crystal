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


### 11.  Spectral network realization (exact WKB, Darboux coordinates, and BPS integers)

Let \(C\) be the Riemann surface of the RG “time” coordinate \\(\\ell\\) (analytically \(C\simeq\\mathbb P^1_\\ell\) with marked points at the poles/zeros below). From the affine leaf and its two-loop deformation (Sec. 4), define the *spectral differential*
\[
\boxed{\;\\lambda(b,b_1;\\ell)=\\mu(\\ell;b,b_1)^{-1}\,d\\ell\;},
\]
where \\(\\mu(\\ell;b,b_1)\\) is the (exactly computed) solution of \(F(\\mu;\\ell)=0\) with
\[
F(\\mu;\\ell)=\\ell+\\frac{1}{b\\mu}-\\frac{b_1}{b^2}\\log\\!\\Bigl(\\frac{b+b_1\\mu}{\\mu}\\Bigr).
\]
The associated *quadratic differential* on \(C\) is
\[
\boxed{\;\\varphi(b,b_1;\\ell)\,d\\ell^{2}=\\bigl(\\mu(\\ell;b,b_1)^{-1}\\bigr)^{2}\,d\\ell^{2}\;}. 
\]

#### Spectral curve and branch data
Introduce the double cover \\(\\pi:\\Sigma\\to C\\) (“spectral curve”)
\[
\boxed{\;\\Sigma:\;y^{2}=\\varphi(b,b_1;\\ell)\;},\qquad \boxed{\;\\lambda=y\,d\\ell\;}
\]
with *branch points* at the zeros of \\(\\varphi\\) (equivalently, \\(\\mu^{-1}(\\ell)=0\\)) and with marked poles at the poles of \\(\\varphi\\) (including \\(\\ell=\\infty\\)). Write \\(\u{1D51D}=\\{\\ell_a\\}\\subset C\\) for the set of branch points; near \\(\\ell_a\\) there are two *sheets* with local coordinate \\(y=\\pm\\sqrt{\\varphi}\\).

#### WKB trajectories and the spectral network
For any *phase* \\(\\theta\\in\\mathbb R/2\\pi\\mathbb Z\\), the *WKB trajectories* of phase \\(\\theta\\) are the integral curves on \(C\) solving
\[
\boxed{\;\\mathrm{Im}\\!\left(e^{-i\\theta}\\!\\int^{\\ell}\\lambda\right)=\\text{const}\;}\quad\\Longleftrightarrow\\quad
\boxed{\;e^{-i\\theta}\\lambda\\in\\mathbb R_{\\ge 0}\,d s\;}
\]
in local arclength \(s\). The *spectral network* at phase \\(\\theta\\) is the union of *finite* WKB trajectories (also called *saddle connections*) emanating from the branch points:
\[
\boxed{\;\\mathcal W_\\theta=\\bigcup_{\\ell_a\\in\\mathfrak b}\\ \{\\text{finite trajectories of phase }\\theta\\ \text{from }\\ell_a\\}.}
\]
*Critical phases* \\(\\theta_c\\) are those for which new finite trajectories appear/disappear; between critical phases the combinatorial type of \\(\\mathcal W_\\theta\\) is constant.

#### Darboux/spectral coordinates and Poisson structure
Fix a symplectic basis of charges \\({\\gamma_i}\\) in \(H_1(\\Sigma,\\mathbb Z)\). Define *central charges* and *Darboux (spectral) coordinates*
\[
\boxed{\;Z_\\gamma=\\oint_\\gamma \\lambda\\in\\mathbb C,\qquad \\mathcal X_\\gamma=\\exp\\!\left(\\oint_\\gamma \\lambda\right)\;}
\]
for any \\(\\gamma\\in H_1(\\Sigma,\\mathbb Z)\\). The intersection pairing \\(\u{27E8}\\cdot,\\cdot\\u{27E9}:H_1(\\Sigma)\\times H_1(\\Sigma)\\to\\mathbb Z\\) induces the standard Poisson brackets
\[
\boxed{\;\\{\\log \\mathcal X_\\gamma,\\ \\log \\mathcal X_{\\gamma'}\\}=\\langle \\gamma,\\gamma'\\rangle\;}. 
\]

#### BPS rays, degeneracies, and wall–crossing
A *BPS ray* in the \\(\\zeta\\)–plane is \\(\u{2113}_\\gamma=\\mathbb R_{>0}\,Z_\\gamma\\). The *BPS index* \\(\\Omega(\\gamma)\\in\\mathbb Z\\) counts (with signs) the finite webs in \\(\\mathcal W_\\theta\\) at the *aligned* phase \\(\\theta=\\arg Z_\\gamma\\). Across a critical phase, the spectral coordinates jump by a *KS/cluster transformation*. With a chosen quadratic refinement sign \\(\\sigma(\\gamma)\\in\\{\\pm1\\}\\),
\[
\boxed{\;\\mathcal K_\\gamma:\ \\mathcal X_\\beta\\ \longmapsto\\ \\mathcal X_\\beta\\(1-\\sigma(\\gamma)\,\\mathcal X_\\gamma)^{\\langle \\beta,\\gamma\\rangle\\,\\Omega(\\gamma)}\;}. 
\]
Let \\(\\theta_\\pm\\) be phases just below/above a wall. The exact wall–crossing identity is the equality of ordered products
\[
\boxed{\;\\prod_{\\arg Z_\\gamma=\\theta_-}\\mathcal K_\\gamma^{\\Omega(\\gamma)}\\ =\\ \\prod_{\\arg Z_\\gamma=\\theta_+}\\mathcal K_\\gamma^{\\Omega(\\gamma)}\;}
\]
(where products are taken in the clockwise order of BPS rays).

#### Exact \\(B_{5}\\) equivariance
The exact \\(B_{5}\\) symmetry acts by signed permutations on sheets; it induces an action \\(w_*:H_1(\\Sigma,\\mathbb Z)\\to H_1(\\Sigma,\\mathbb Z)\\). Equivariance is *exactly* checked as
\[
\boxed{\;Z_{w_*\\gamma}=Z_\\gamma,\quad \\mathcal X_{w_*\\gamma}=\\mathcal X_\\gamma,\quad \\Omega(w_*\\gamma)=\\Omega(\\gamma),\\qquad \\forall\,w\\in W(B_5)\;}
\]
and at the network level by a sheet relabeling that takes \\(\\mathcal W_\\theta\\) to itself.

---

## Two-loop deformation of the network
With the two-loop deformed \\(\\mu(\\ell;b,b_1)\\), define
\[
\boxed{\;\\lambda(b,b_1;\\ell)=\\mu(\\ell;b,b_1)^{-1}\,d\\ell,\qquad \\varphi(b,b_1;\\ell)=\\bigl(\\mu(\\ell;b,b_1)^{-1}\\bigr)^2\;}
\]
and construct \\(\\mathcal W_\\theta(b,b_1)\\) accordingly. On *generic* deformations (no BPS walls crossed) the ordered product of KS factors is constant:
\[
\boxed{\;\\frac{d}{db_1}\\Big|_{\\text{no wall}} \\ \prod_{\\arg Z_\\gamma=\\theta}\\mathcal K_\\gamma^{\\Omega(\\gamma)}\\ =\\ 0\;}. 
\]
When \(b_1\) crosses a wall, the set of factors changes by a *cluster flip* but preserves the product equality above (Kontsevich–Soibelman).

---

## Spectral receipts and the ledger

**Network capsule.** Serialize the exact combinatorics of \\(\\mathcal W_\\theta\\):
\[
\boxed{\ \texttt{spec\\_net.json}=\\Bigl\\{\ b,b_1,\\ \\mu_0,\\ \\{\\ell_a\\\\}\\_{\\text{branch}},\\ \\{\\theta_c\\\\}\\_{\\text{critical}},\\ \\texttt{walls}=\\{(\\theta,\\text{edges},\\text{endpoints})\\},\\ \\texttt{sheets},\\ \\texttt{monodromy}\\Bigr\\}\\ ,}
\]
\[
\boxed{\ h_{\\mathrm{net}}=\\mathrm{Hash}_{256}\\bigl(\\texttt{\"SPEC\\_NET\"}\\parallel \\texttt{spec\\_net.json}\\bigr).}
\]

**Darboux/charge capsule.** Record periods, intersection, and coordinates:
\[
\boxed{\ \\texttt{spec\\_coords.json}=\\Bigl\\{\\ \\{\\gamma_i\\},\\ I_{ij}=\\langle\\gamma_i,\\gamma_j\\rangle,\\ Z_{\\gamma_i},\\ \\mathcal X_{\\gamma_i}\\Bigr\\}\\ ,\quad
h_{\\mathrm{coords}}=\\mathrm{Hash}_{256}\\bigl(\\texttt{\"SPEC\\_COORDS\"}\\parallel \\texttt{spec\\_coords.json}\\bigr).}
\]

**BPS capsule.** Record integer indices and KS factors (per wall and ordering):
\[
\boxed{\ \\texttt{spec\\_bps.json}=\\Bigl\\{\\ (\\gamma,\\Omega(\\gamma),\\sigma(\\gamma))\\_{\\text{all BPS}},\\ \\texttt{KS\\_order}(\\theta)=\\prod \\mathcal K_\\gamma^{\\Omega(\\gamma)}\\Bigr\\}\\ ,}
\]
\[
\boxed{\ h_{\\mathrm{bps}}=\\mathrm{Hash}_{256}\\bigl(\\texttt{\"SPEC\\_BPS\"}\\parallel \\texttt{spec\\_bps.json}\\bigr).}
\]

**Equivariance checks.** For each \(w\\in W(B_5)\),
\[
\boxed{\ \\texttt{spec\\_equiv.json}(w)=\\Bigl\\{\\ w,\\ Z_{w_*\\gamma}\\overset{?}{=}Z_\\gamma,\\ \\mathcal X_{w_*\\gamma}\\overset{?}{=}\\mathcal X_\\gamma,\\ \\Omega(w_*\\gamma)\\overset{?}{=}\\Omega(\\gamma)\\Bigr\\},}
\]
\[
\boxed{\ h_{\\mathrm{equiv}}(w)=\\mathrm{Hash}_{256}\\bigl(\\texttt{\"SPEC\\_EQUIV\"}\\parallel \\texttt{spec\\_equiv.json}(w)\\bigr).}
\]

**Wall–crossing receipts.** For adjacent phases \\(\\theta_\\pm\\),
\[
\boxed{\ \\texttt{spec\\_wc.json}(\\theta_\\pm)=\\Bigl\\{\\ \\theta_\\pm,\\ \\texttt{KS\\_order}(\\theta_-),\\ \\texttt{KS\\_order}(\\theta_+),\\ \\texttt{ok}=[\\texttt{KS\\_order}(\\theta_-)\\overset{?}{=}\\texttt{KS\\_order}(\\theta_+)]\\Bigr\\},}
\]
\[
\boxed{\ h_{\\mathrm{wc}}(\\theta_\\pm)=\\mathrm{Hash}_{256}\\bigl(\\texttt{\"SPEC\\_WC\"}\\parallel \\texttt{spec\\_wc.json}(\\theta_\\pm)\\bigr).}
\]

**Deformation receipts.** For \(b_1\\to b_1'\) across a *regular* path (no walls),
\[
\boxed{\ \\texttt{spec\\_deform.json}=\\Bigl\\{\\ b_1\\to b_1',\\ \\theta,\\ \\texttt{KS\\_order}(\\theta)\\ \\text{constant?}\\Bigr\\},\quad
h_{\\mathrm{def}}=\\mathrm{Hash}_{256}\\bigl(\\texttt{\"SPEC\\_DEF\"}\\parallel \\texttt{spec\\_deform.json}\\bigr).}
\]

**Spectral digest.** Aggregate with a Merkle root to localize failures:
\[
\boxed{\ h_{\\mathrm{spec}}=\\mathrm{Merkle}_{256}\\Bigl(h_{\\mathrm{net}},\\ h_{\\mathrm{coords}},\\ h_{\\mathrm{bps}},\\ \\{h_{\\mathrm{equiv}}(w)\\}\\_{w\\in W(B_5)},\\ \\{h_{\\mathrm{wc}}(\\theta_\\pm)\\},\\ h_{\\mathrm{def}}\\Bigr).}
\]

**Acceptance predicate.** The ledger accepts the spectral layer iff:
\[
\boxed{\ \\Omega(\\gamma)\\in\\mathbb Z\\ \forall\\gamma;\\ \\texttt{ok}= \\text{true in all } \\texttt{spec\\_wc.json};\\ \\text{all equivariance checks hold}. }
\]
Upon acceptance, \\(h_{\\mathrm{spec}}\\) enters the master root \\(H_\\tau\\); any mismatch (non-integer BPS count, failed KS identity, failed \\(B_5\\) equivariance) flips the corresponding \\texttt{ok} and breaks the master hash at the spectral leaf, isolating the fault.


### 12.  p-adic interpolation (rigid RG, analytic Weyl action, whitening, Darboux, Iwasawa) 

Fix an odd prime \(p\) with \(p\nmid \mathrm{den}(b\,\mu_0)\). Work over the non-Archimedean base
\[
\boxed{\;k_p=\mathbb Q_p(b)\;,}
\]
and choose Teichmüller lifts for units: for any \(u\in\mathbb Z_p^\times\),
\[
\boxed{\;u=\omega(u)\,\langle u\rangle,\quad \omega(u)^{p-1}=1,\ \ \langle u\rangle\in 1+p\mathbb Z_p,\quad \log_p(u):=\log_p(\langle u\rangle)\;.}
\]

#### 12.1  p-adic RG equation and Hensel–Newton flow
Define the p-adic deformation of the first-integral equation by replacing logarithms with \(\log_p\) on the domain where they converge:
\[
\boxed{\;F_p(\mu;\ell):=\ell+\frac{1}{b\mu}-\frac{b_1}{b^{2}}\Bigl(\log_p(b+b_1\mu)-\log_p(\mu)\Bigr)=0\;,}
\]
with derivative (valid on the analytic domain where both logs are defined)
\[
\boxed{\;F_p'(\mu)= -\frac{1}{b\mu^{2}}-\frac{b_{1}}{b^{2}}\Bigl(\frac{b_1}{b+b_1\mu}-\frac{1}{\mu}\Bigr)\;.}
\]
Newton–Hensel iteration:
\[
\boxed{\;\mu_{n+1}=\mu_n-\frac{F_p(\mu_n;\ell)}{F_p'(\mu_n)}\;,}
\]
converges quadratically provided a Hensel condition holds at the seed \(\mu_0^{\mathrm{seed}}\):
\[
\boxed{\;v_p\Bigl(F_p(\mu_0^{\mathrm{seed}};\ell)\Bigr)\ >\ 2\,v_p\Bigl(F_p'(\mu_0^{\mathrm{seed}})\Bigr)\;.}
\]
The p-adic period of the leaf’s closed 1-form remains
\[
\boxed{\;\lambda_p(\ell)=\mu(\ell)^{-1}\,d\ell,\qquad \mathrm{per}_p(\omega)=(\mu_0^{(p)})^{-1}\in\mathbb Z_p\;,}
\]
with \(\mu_0^{(p)}=\omega(\mu_0)\in\mathbb Z_p^\times\) the Teichmüller lift (Sec. 6).

#### 12.2  Rigid domain and Haar normalization
Choose a closed p-adic disc (or annulus) \(D\subset\mathbb Z_p\) on which all series converge (logs and Newton flow). Normalize the Haar measure \(d\ell\) so that
\[
\boxed{\;\int_D 1\,d\ell=1\;.}
\]

#### 12.3  p-adic sections, covariance, and whitening
Define p-adic log-sections
\[
\boxed{\;s_i(\ell)=\log_p\!\Bigl(\frac{m_i(\ell)}{m_0(\ell)}\Bigr),\qquad \bar s_i=\int_D s_i\,d\ell\;,}
\]
and the rigid covariance (a symmetric, non-degenerate bilinear form over \(k_p\))
\[
\boxed{\;\Sigma^{(p)}_{ij}=\int_D \bigl(s_i-\bar s_i\bigr)\bigl(s_j-\bar s_j\bigr)\,d\ell\in k_p\;.}
\]
Compute an inverse square-root via a p-adic Denman–Beavers iteration with scaling. Choose \(\alpha\in k_p^\times\) such that \(\|I-\alpha\Sigma^{(p)}\|_p<1\), set
\[
\boxed{\;Y_0=I,\quad Z_0=\alpha\Sigma^{(p)}\;,}
\]
and iterate
\[
\boxed{\;Y_{n+1}=\tfrac12\,Y_n\bigl(3I-Z_nY_n\bigr),\qquad Z_{n+1}=\tfrac12\,\bigl(3I-Z_nY_n\bigr)Z_n\;,}
\]
which converges p-adically to \(Y_\infty=(\alpha\Sigma^{(p)})^{-1/2}\), \(Z_\infty=(\alpha\Sigma^{(p)})^{1/2}\). Then set
\[
\boxed{\;W_p=\sqrt{\alpha}\,Y_\infty\in \mathrm{GL}_5(k_p),\qquad W_p^{T}\,\Sigma^{(p)}\,W_p=I\;.}
\]
Exact \(B_5\) equivariance is checked by signed permutation matrices \(P_w\) (entries \(\pm1\in\mathbb Z_p\)):
\[
\boxed{\;W_p\,P_w\,\Sigma^{(p)}\,P_w^{T}\,W_p^{T}=O_w^{(p)},\quad (O_w^{(p)})^{T}O_w^{(p)}=I,\ \ w\in W(B_5)\;.}
\]

#### 12.4  p-adic chamber index and receipts
For \(c\in\mathbb Q^5\subset k_p^5\),
\[
\boxed{\;\rho^{(p)}=W_p\,c,\qquad r^{(p)}=(\Sigma^{(p)})^{-1}c\;,}
\]
and the chamber predicate is
\[
\boxed{\;r^{(p)}\in \mathcal C\quad\Longleftrightarrow\quad \text{run accepted at }p\;.}
\]
Record verified valuations for acceptance at precision \(N\):
\[
\boxed{\;v_p\bigl(F_p(\mu_N)\bigr)\ge N,\quad \|W_p^{T}\Sigma^{(p)}W_p-I\|_p\le p^{-N}\;.}
\]

#### 12.5  p-adic Darboux coordinates and analytic Weyl action
Define p-adic central charges by Coleman integration on the spectral curve \(\Sigma\) (Sec. 11):
\[
\boxed{\;Z_\gamma^{(p)}=\oint_\gamma \lambda_p\in k_p,\qquad \gamma\in H_1(\Sigma,\mathbb Z)\;,}
\]
and (on the convergence domain \(v_p(Z_\gamma^{(p)})>0\)) the p-adic Darboux coordinates
\[
\boxed{\;\mathcal X_\gamma^{(p)}=\exp_p\!\bigl(Z_\gamma^{(p)}\bigr)\;,}
\]
with the standard Poisson brackets (intersection pairing unchanged):
\[
\boxed{\;\{\log \mathcal X_\gamma^{(p)},\log \mathcal X_{\gamma'}^{(p)}\}=\langle\gamma,\gamma'\rangle\;.}
\]
Exact \(B_5\)-equivariance:
\[
\boxed{\;Z_{w_*\gamma}^{(p)}=Z_\gamma^{(p)},\quad \mathcal X_{w_*\gamma}^{(p)}=\mathcal X_\gamma^{(p)}\;.}
\]

#### 12.6  Iwasawa interpolation (cyclotomic tower)
Let \(\Lambda=\mathbb Z_p[[T]]\) and \(\kappa:\mathbb Z_p^\times\to \Lambda^\times\) the universal character \(\kappa(u)=(1+T)^{\log_p(u)/\log_p(1+p)}\). A \(\Lambda\)–adic family of periods/intersections is a function
\[
\boxed{\;L^{(p)}(s)=\int_{\mathbb Z_p^\times} u^{\,s}\,d\nu(u)\in\Lambda\;,}
\]
such that for integers \(s\) in a prescribed congruence class,
\[
\boxed{\;L^{(p)}(s)=\sum_{\gamma}\Omega(\gamma)\,\bigl(Z_\gamma^{(p)}\bigr)^{s}\quad\text{(finite sum on a wall-finite window)}\;,}
\]
with \(\nu\) a bounded p-adic measure determined by the motivic capsule (Sec. 1/6). Coherence along the Iwasawa tower \(\mathbb Q_p(\zeta_{p^n})\) is enforced by the distribution relation
\[
\boxed{\;\nu(a+p^{n}\mathbb Z_p)=\sum_{j=0}^{p-1}\nu(a+jp^{n}+p^{n+1}\mathbb Z_p)\;.}
\]

#### 12.7  p-adic coupling to anomaly and master hash
At the canonical test pair \((M_\star,f_\rho)\) (Sec. 10),
\[
\boxed{\;e^{\,\log B^{(p)}}:=Z_{\mathrm{anom}}^{(p)}(M_\star,f_\rho)\in \mathbb C_p^\times,\qquad \log B^{(p)}\equiv \log_p Z_{\mathrm{anom}}^{(p)}\ (\mathrm{mod}\ p^N)\;,}
\]
and cross-place compatibility (on \(p\)–integral data) is recorded as
\[
\boxed{\;\iota_p\bigl(\mathrm{per}(\omega)\bigr)\equiv \mathrm{per}_p(\omega)\ (\mathrm{mod}\ p^N),\quad \iota_p\bigl(Z_\gamma\bigr)\equiv Z_\gamma^{(p)}\ (\mathrm{mod}\ p^N)\;.}
\]

---

## p-adic receipt capsules and acceptance

**RG capsule (p-adic):**
\[
\boxed{\ \texttt{padic\_rg.json}=\bigl\{p,\ D,\ b,b_1,\ \mu_0^{(p)},\ \texttt{hensel}=[v_p(F_p(\mu_0))>2v_p(F'_p(\mu_0))],\ \texttt{res}=v_p(F_p(\mu_N)),\ N\bigr\},}
\]
\[
\boxed{\ h_{\mathrm{rg}}^{(p)}=\mathrm{Hash}_{256}\bigl(\texttt{\"PADIC\_RG\"}\parallel \texttt{padic\_rg.json}\bigr).}
\]

**Whitening capsule (p-adic):**
\[
\boxed{\ \texttt{padic\_white.json}=\bigl\{p,\ \Sigma^{(p)},\ \alpha,\ W_p,\ \delta=\|W_p^{T}\Sigma^{(p)}W_p-I\|_p,\ N\bigr\},}
\]
\[
\boxed{\ h_{\mathrm{white}}^{(p)}=\mathrm{Hash}_{256}\bigl(\texttt{\"PADIC\_WHITE\"}\parallel \texttt{padic\_white.json}\bigr).}
\]

**Darboux capsule (p-adic):**
\[
\boxed{\ \texttt{padic\_coords.json}=\bigl\{p,\ \{\gamma_i\},\ Z_{\gamma_i}^{(p)},\ \mathcal X_{\gamma_i}^{(p)},\ \texttt{dom}=[v_p(Z_{\gamma_i}^{(p)})>0]\bigr\},}
\]
\[
\boxed{\ h_{\mathrm{coords}}^{(p)}=\mathrm{Hash}_{256}\bigl(\texttt{\"PADIC\_COORDS\"}\parallel \texttt{padic\_coords.json}\bigr).}
\]

**Equivariance capsule (p-adic):**
\[
\boxed{\ \texttt{padic\_equiv.json}(w)=\bigl\{w,\ Z_{w_*\gamma}^{(p)}\overset{?}{=}Z_\gamma^{(p)},\ \mathcal X_{w_*\gamma}^{(p)}\overset{?}{=}\mathcal X_\gamma^{(p)}\bigr\},}
\]
\[
\boxed{\ h_{\mathrm{equiv}}^{(p)}(w)=\mathrm{Hash}_{256}\bigl(\texttt{\"PADIC\_EQUIV\"}\parallel \texttt{padic\_equiv.json}(w)\bigr).}
\]

**Iwasawa capsule:**
\[
\boxed{\ \texttt{padic\_iwasawa.json}=\bigl\{\Lambda,\ \nu,\ \texttt{dist\_ok},\ L^{(p)}(T)\bigr\},\qquad
h_{\mathrm{iwa}}^{(p)}=\mathrm{Hash}_{256}\bigl(\texttt{\"PADIC\_IWASAWA\"}\parallel \texttt{padic\_iwasawa.json}\bigr).}
\]

**p-adic digest and acceptance:**
\[
\boxed{\ h_{\mathrm{p}}=\mathrm{Merkle}_{256}\Bigl(h_{\mathrm{rg}}^{(p)},\ h_{\mathrm{white}}^{(p)},\ h_{\mathrm{coords}}^{(p)},\ \{h_{\mathrm{equiv}}^{(p)}(w)\},\ h_{\mathrm{iwa}}^{(p)}\Bigr),}
\]
\[
\boxed{\ \text{accept at }p\iff \begin{cases}
v_p(F_p(\mu_N))\ge N,\\[2pt]
\|W_p^{T}\Sigma^{(p)}W_p-I\|_p\le p^{-N},\\[2pt]
\text{all p-adic equivariance checks true},\\[2pt]
\text{Iwasawa distribution relation holds.}
\end{cases}}
\]
Upon acceptance, include \(h_{\mathrm{p}}\) among the place-tagged leaves in the master Merkle root \(H_\tau\). Any failure (Newton residual too small, whitening not orthonormal to precision, broken \(B_5\) equivariance, or Iwasawa incoherence) flips the corresponding \(\texttt{ok}\) and isolates the p-adic fault by its sibling path.


### 13.  Categorified index on the chamber (B₅–equivariant complex, Euler class, Ext–pairings, and receipts)

Let \(\mathsf{Rep}_{\mathbb Q}(B_{5})\) be the semisimple tensor category of finite–dimensional \(\mathbb Q\)–linear representations of the hyperoctahedral group \(B_{5}\simeq(\mathbb Z/2\mathbb Z)^{5}\rtimes S_{5}\). Fix the exact \(B_{5}\)–action coming from whitening (Sec. 2) and the chamber \(\mathcal C\) (Sec. 3).

#### 13.1  The B₅–equivariant index as a virtual representation

Choose a finite \(B_{5}\)–equivariant cochain complex
\[
\boxed{\;C^\bullet:\quad 0\longrightarrow C^0\xrightarrow{\,d^0\,}C^1\xrightarrow{\,d^1\,}\cdots\xrightarrow{\,d^{m-1}\,}C^{m}\longrightarrow 0\;,\qquad C^i\in\mathsf{Rep}_{\mathbb Q}(B_{5}).}
\]
Differentials are \(B_{5}\)–equivariant:
\[
\boxed{\;d^{i}\,\rho_{C^i}(g)=\rho_{C^{i+1}}(g)\,d^{i}\quad\forall g\in B_{5},\qquad d^{i+1}\circ d^{i}=0\;.}
\]
The \(B_{5}\)–equivariant index is the class in the Grothendieck ring \(K^0_{B_{5}}\):
\[
\boxed{\;\mathrm{Ind}_{B_{5}}(C^\bullet)=\sum_{i=0}^{m}(-1)^i\,[C^i]=\sum_{i=0}^{m}(-1)^i\,[H^i(C^\bullet)]\ \in K^0_{B_{5}}.}
\]
Its class function (graded character at \(t=1\)) is
\[
\boxed{\;\chi_{B_{5}}(g)=\sum_{i=0}^{m}(-1)^i\,\mathrm{Tr}\!\left(g\mid C^i\right)=\sum_{i=0}^{m}(-1)^i\,\mathrm{Tr}\!\left(g\mid H^i\right),\qquad g\in B_{5}.}
\]

If a grading \(\deg:C^\bullet\to\mathbb Z\) (e.g. filtration from the RG leaf) is fixed, define the refined index
\[
\boxed{\;\chi_{B_{5}}(g;t)=\sum_{i,k}(-1)^i\,t^{\,k}\,\mathrm{Tr}\!\left(g\mid C^i[k]\right),\qquad \chi_{B_{5}}(g;1)=\chi_{B_{5}}(g).}
\]

#### 13.2  Decomposition into irreducibles and non-negativity in cohomology

Let \(\{V_\lambda\}_{\lambda\in\widehat{B_{5}}}\) be a complete set of irreducibles with characters \(\chi_\lambda\). Multiplicity extraction in degree \(i\) is
\[
\boxed{\;m_\lambda^{(i)}=\frac{1}{|B_{5}|}\sum_{g\in B_{5}}\chi_\lambda(g^{-1})\,\mathrm{Tr}\!\left(g\mid C^i\right)\ \in\ \mathbb Z_{\ge 0},}
\]
and in cohomology
\[
\boxed{\;n_\lambda^{(i)}=\frac{1}{|B_{5}|}\sum_{g\in B_{5}}\chi_\lambda(g^{-1})\,\mathrm{Tr}\!\left(g\mid H^i\right)\ \in\ \mathbb Z_{\ge 0}.}
\]
The virtual multiplicities are the alternating sums
\[
\boxed{\;\nu_\lambda=\sum_{i}(-1)^i n_\lambda^{(i)}=\frac{1}{|B_{5}|}\sum_{g\in B_{5}}\chi_\lambda(g^{-1})\,\chi_{B_{5}}(g)\ \in\ \mathbb Z.}
\]

#### 13.3  Ext–pairings and obstructions

Work in \(D^{b}\!\big(\mathsf{Rep}_{\mathbb Q}(B_{5})\big)\). For \(X^\bullet,Y^\bullet\) define the equivariant Ext–pairing
\[
\boxed{\;\langle X^\bullet,Y^\bullet\rangle_{\!\mathrm{Ext}}=\sum_{i\in\mathbb Z}(-1)^i\,\dim_{\mathbb Q}\mathrm{Ext}^{\,i}_{B_{5}}(X^\bullet,Y^\bullet)\ \in\ \mathbb Z.}
\]
Self-pairing detects obstructions to formal deformations of \(X^\bullet\):
\[
\boxed{\;\mathrm{Obs}(X^\bullet)\ \subseteq\ \mathrm{Ext}^{2}_{B_{5}}(X^\bullet,X^\bullet),\qquad \text{infinitesimal deformations are in }\ \mathrm{Ext}^{1}_{B_{5}}(X^\bullet,X^\bullet).}
\]

A character-valued Ext–index (refined by conjugacy class) is
\[
\boxed{\;\Xi_{X,Y}(g)=\sum_{i}(-1)^i\,\mathrm{Tr}\!\left(g\mid \mathrm{Ext}^{\,i}_{B_{5}}(X^\bullet,Y^\bullet)\right),\qquad g\in B_{5}.}
\]

#### 13.4  Wall-crossing = derived equivalence (auditable)

Two chambers \(\mathcal C_{\pm}\) are related by a kernel \(K\in D^{b}\!\big(\mathsf{Rep}_{\mathbb Q}(B_{5})\big)\) that implements a Fourier–Mukai–type autoequivalence
\[
\boxed{\;\Phi_{K}:D^{b}\!\to D^{b}\!,\qquad \Phi_{K}(C^\bullet_{-})\ \simeq\ C^\bullet_{+}.}
\]
On \(K^0_{B_{5}}\) this induces
\[
\boxed{\;[\Phi_{K}(C^\bullet_{-})]=[C^\bullet_{+}],\qquad \chi_{B_{5}}^{(-)}(g)=\chi_{B_{5}}^{(+)}(g)\quad\forall g.}
\]
A *certificate of quasi-isomorphism* is a triple of \(B_{5}\)–equivariant maps \((f^\bullet,g^\bullet,h^\bullet)\) with
\[
\boxed{\;f^{i}:C^{i}_{-}\!\to C^{i}_{+},\quad g^{i}:C^{i}_{+}\!\to C^{i}_{-},\quad h^{i}:C^{i}_{-}\!\to C^{i-1}_{-}}
\]
satisfying the chain-homotopy identities
\[
\boxed{\;g^\bullet f^\bullet-\mathrm{id}=d h+h d,\qquad f^\bullet g^\bullet-\mathrm{id}=d' h'+h' d',\qquad d^{\prime}f=fd,}
\]
which imply \(C^\bullet_{-}\simeq C^\bullet_{+}\) in \(D^{b}\) and preserve the index.

#### 13.5  Relative index on the chamber

Given a null (randomized) chamber complex \(C^\bullet_{\mathrm{null}}\) and the canonical chamber complex \(C^\bullet\), define the *relative* \(B_{5}\)–index
\[
\boxed{\;\Delta\mathrm{Ind}_{B_{5}}=\mathrm{Ind}_{B_{5}}(C^\bullet)-\mathrm{Ind}_{B_{5}}(C^\bullet_{\mathrm{null}})\ \in K^0_{B_{5}},}
\]
and its scalar reduction via the augmentation \(\varepsilon:K^0_{B_{5}}\to \mathbb Z\) (dimension)
\[
\boxed{\;\varepsilon\!\left(\Delta\mathrm{Ind}_{B_{5}}\right)=\sum_{i}(-1)^i\bigl(\dim H^{i}-\dim H^{i}_{\mathrm{null}}\bigr)\ \in \mathbb Z.}
\]
More generally, the log-Bayes observable (Sec. 3) is the metric-normalized scalar shadow of a class function:
\[
\boxed{\;\log B=\mathcal F\!\left(\chi_{B_{5}}-\chi^{\mathrm{null}}_{B_{5}};\,\Sigma\right),}
\]
for an explicit linear functional \(\mathcal F\) determined by the covariance \(\Sigma\) (fixed once for the corridor).

---

## Receipts for the categorified index

**(a) Complex capsule (equivariant matrices).** Serialize differentials as matrices over the group algebra \(\mathbb Q[B_{5}]\):
\[
\boxed{\ \texttt{index\_complex.json}=\Bigl\{\ n_i,\ d^{i}\in \mathrm{Mat}_{n_{i+1}\times n_i}\!\big(\mathbb Q[B_{5}]\big),\ \texttt{check}=[d^{i+1}\! \cdot d^{i}=0]_{i}\ \Bigr\},}
\]
\[
\boxed{\ h_{\mathrm{cmp}}=\mathrm{Hash}_{256}\bigl(\texttt{\"INDEX\_CPLX\"}\parallel \texttt{index\_complex.json}\bigr).}
\]

**(b) Character capsule (degree-wise and Euler).**
\[
\boxed{\ \texttt{index\_char.json}=\Bigl\{\ \chi_{C^i}(g)\ \text{per conjugacy class and }i,\ \chi_{B_{5}}(g)=\sum_i(-1)^i\chi_{C^i}(g)\ \Bigr\},}
\]
\[
\boxed{\ h_{\mathrm{char}}=\mathrm{Hash}_{256}\bigl(\texttt{\"INDEX\_CHAR\"}\parallel \texttt{index\_char.json}\bigr).}
\]

**(c) Homology capsule (multiplicities in \(H^{i}\)).**
\[
\boxed{\ \texttt{index\_hom.json}=\Bigl\{\ n_\lambda^{(i)}\ \text{for all }\lambda\in\widehat{B_{5}},\ i=0,\dots,m\ \Bigr\},}
\]
\[
\boxed{\ h_{\mathrm{hom}}=\mathrm{Hash}_{256}\bigl(\texttt{\"INDEX\_HOM\"}\parallel \texttt{index\_hom.json}\bigr).}
\]

**(d) Orthogonality and non-negativity checks.**
\[
\boxed{\ \texttt{index\_checks.json}=\Bigl\{\ \langle \chi_{B_{5}},\chi_\lambda\rangle=\nu_\lambda,\ \ n_\lambda^{(i)}\ge 0,\ \ \sum_i(-1)^in_\lambda^{(i)}=\nu_\lambda\ \Bigr\},}
\]
\[
\boxed{\ h_{\mathrm{chk}}=\mathrm{Hash}_{256}\bigl(\texttt{\"INDEX\_CHECKS\"}\parallel \texttt{index\_checks.json}\bigr).}
\]

**(e) Ext–pairing capsule (obstructions).**
\[
\boxed{\ \texttt{index\_ext.json}=\Bigl\{\ \dim \mathrm{Ext}^{\,i}_{B_{5}}(C^\bullet,C^\bullet),\ \Xi_{C,C}(g)\ \Bigr\},}
\]
\[
\boxed{\ h_{\mathrm{ext}}=\mathrm{Hash}_{256}\bigl(\texttt{\"INDEX\_EXT\"}\parallel \texttt{index\_ext.json}\bigr).}
\]

**(f) Wall-crossing/quasi-isomorphism certificate.**
\[
\boxed{\ \texttt{index\_qiso.json}=\Bigl\{\ f^\bullet,g^\bullet,h^\bullet\ \text{as } \mathbb Q[B_{5}]\text{–matrices},\ \texttt{ok}=[g f-\mathrm{id}=d h+h d,\ f g-\mathrm{id}=d' h'+h' d']\ \Bigr\},}
\]
\[
\boxed{\ h_{\mathrm{qiso}}=\mathrm{Hash}_{256}\bigl(\texttt{\"INDEX\_QISO\"}\parallel \texttt{index\_qiso.json}\bigr).}
\]

**(g) Relative index capsule (vs. null chamber).**
\[
\boxed{\ \texttt{index\_rel.json}=\Bigl\{\ \chi_{B_{5}}-\chi^{\mathrm{null}}_{B_{5}},\ \Delta\mathrm{Ind}_{B_{5}},\ \varepsilon(\Delta\mathrm{Ind}_{B_{5}})\ \Bigr\},}
\]
\[
\boxed{\ h_{\mathrm{rel}}=\mathrm{Hash}_{256}\bigl(\texttt{\"INDEX\_REL\"}\parallel \texttt{index\_rel.json}\bigr).}
\]

**(h) Index digest and acceptance.**
\[
\boxed{\ h_{\mathrm{index}}=\mathrm{Merkle}_{256}\Bigl(\,h_{\mathrm{cmp}},\,h_{\mathrm{char}},\,h_{\mathrm{hom}},\,h_{\mathrm{chk}},\,h_{\mathrm{ext}},\,h_{\mathrm{qiso}},\,h_{\mathrm{rel}}\Bigr).}
\]
The ledger **accepts** the categorified-index layer iff
\[
\boxed{\;\begin{aligned}
&d^{i+1}d^{i}=0\ \text{for all }i;\\
&\chi_{B_{5}}(g)=\sum_i(-1)^i\mathrm{Tr}\!\left(g\mid H^i\right)\ \text{for all conjugacy classes};\\
&n_\lambda^{(i)}\in\mathbb Z_{\ge 0},\ \ \sum_i(-1)^i n_\lambda^{(i)}=\nu_\lambda\ \text{for all }\lambda;\\
&\texttt{ok}=\text{true in }\texttt{index\_qiso.json}\ \text{(when wall-crossing is claimed).}
\end{aligned}}
\]
On acceptance, \(h_{\mathrm{index}}\) enters the master root \(H_{\tau}\); any failed check flips the corresponding \(\texttt{ok}\) and isolates the index fault by its Merkle sibling path.

