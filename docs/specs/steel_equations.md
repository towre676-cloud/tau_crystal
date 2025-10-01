# Steel Equations: Hash‑Bound Formal Spec

_This file is written verbatim from the tightened specification, with equations intact._

### 1.  The affine RG leaf as a relative motive

Work over the tannakian base field \(k=\mathbb Q(b)\). Regard the leaf as the pair \(\bigl(U,\omega\bigr)\) with \(U=\mathbb A^1_k\setminus\{0\}\) and
\[
\boxed{\;\omega=\frac{d\mu}{\mu^{2}}+b\,d\ell\;}
\]
satisfying the first integral
\[
I(\mu,\ell)=\int\omega=\mu^{-1}+b\ell=\mu_0^{-1},\qquad \mu_0\in\mathbb Q_{>0}.
\]
For the de Rham realization, it is cleaner to pin a \(k\)–basis and a marked class rather than a free line with no anchor:
\[
\boxed{\;\mathsf M_{\mathrm{dR}}=(H^1_{\mathrm{dR}}(U/k),\,[\omega])\cong \bigl(k\cdot[\mu^{-2}d\mu],\;[\mu^{-2}d\mu+b\,d\ell]\bigr)\;}
\]
and for the Betti realization choose a reference loop \(\gamma\) in a fiber of \(I\) so that
\[
\boxed{\;\mathsf M_{\mathrm B}=(H_1(U(\mathbb C),\mathbb Z),\,[\gamma])\cong(\mathbb Z\cdot[\gamma],\,[\gamma])\;}. 
\]
The comparison \(\mathrm{comp}_{\mathrm B,\mathrm{dR}}\) is then fixed by the marked data,
\[
\int_{\gamma}\omega=\mathrm{per}(\omega)=\mu_0^{-1},
\]
and the motivic Galois group is the tannakian automorphism group of the fiber functor on the rigid subcategory \(\langle \mathsf M\rangle\). In this elementary case it is a one–dimensional torus or its unipotent extension depending on whether you allow the trivial \(d\ell\) direction; to avoid a dimensionally inconsistent exponential, define the monodromy on the first integral rather than on \(\mu\):
\[
\boxed{\;T:\;I\longmapsto I+2\pi i\,n,\qquad n\in\mathbb Z\;}
\]
and view \(T\) as acting by deck transformations on the level sets of \(I\). The motive capsule must serialize the *marked* realizations and the comparison, not only the numbers they produce:
\[
\boxed{\texttt{motive.json}=\Bigl\{\;k=\mathbb Q(b),\;\mu_0,\;[\omega],\;[\gamma],\;\mathrm{per}(\omega),\;T\;\Bigr\}}
\]
together with a domain‑separated digest
\[
\boxed{\;h_{\mathsf M}=\mathrm{Hash}_{256}\bigl(\texttt{"MOTIVE"}\parallel\texttt{motive.json}\bigr)\;}
\]
so that different capsules cannot collide by construction.

### 2.  Whitening as an isometry of the motivic Gramian

Define the log‑sections \(s_i(\ell)=\log\!\bigl(m_i(\ell)/m_0(\ell)\bigr)\) with \(ds_i/d\ell=b(1-\alpha_i)\). To make the Gramian a true covariance, integrate against a finite, declared measure on a compact \(\ell\)–interval \([\ell_-,\ell_+]\) belonging to a fixed level set of \(I\), and normalize:
\[
\boxed{\;\Sigma_{ij}=\frac{1}{\ell_+-\ell_-}\int_{\ell_-}^{\ell_+}\Bigl(s_i(\ell)-\bar s_i\Bigr)\Bigl(s_j(\ell)-\bar s_j\Bigr)\,d\ell,\quad \bar s_i=\frac{1}{\ell_+-\ell_-}\int_{\ell_-}^{\ell_+} s_i\,d\ell\;}
\]
so that \(\Sigma\) is positive definite. The whitening operator is the symmetric inverse square root
\[
\boxed{\;W=\Sigma^{-1/2},\qquad W^T\Sigma W=I_5\;}
\]
and exact \(B_5\) symmetry acts by signed permutations \(w\in W(B_5)\) on the index set. The equivariance statement is then
\[
\boxed{\;W\,\Sigma\bigl(w\cdot s\bigr)\,W^{T}=O_w\;\;\Longleftrightarrow\;\;W\,P_w\Sigma(s)P_w^{T}W^{T}=O_w,\quad O_w\in \mathrm O(5)\;}
\]
where \(P_w\) is the signed permutation matrix for \(w\). This pins the chamber \(\mathcal C\) canonically once and for all.

Algebraicity deserves one caveat: \(\Sigma\) may contain transcendental entries due to logs; what is exact is its *construction* from the declared measure and sections and its *equivariance* under \(W(B_5)\), which the receipts certify. Where you need algebraicity, elevate to the motivic covariance built from pairings in the de Rham fiber; the numerically realized \(\Sigma\) becomes a comparison shadow of that motivic Gramian.

### 3.  The chamber index as a rational point

For \(c\in\mathbb Q^5\) define
\[
\boxed{\;\rho^{*}=Wc,\qquad r^{*}=\Sigma^{-1}c\;}
\]
and take \(\sigma\in S_5\) to order \(|\rho^*|\) strictly. The falsifiability clause should bind the *run*, not the motive capsule: if \(r^{*}\notin \mathcal C\) the run violates the exact symmetry contract, but the motive’s hash is still the same object. The right attestation is
\[
\boxed{\;\text{run is valid}\;\Longleftrightarrow\; r^{*}\in\mathcal C\;\text{ and }\;W\,P_w\Sigma P_w^{T}W^{T}=O_w\;\;\forall w\in W(B_5)\;}
\]
and it is this predicate that the ledger enforces for the receipt.

For the log‑Bayes expression, specify the unit ball and the induced Gaussian metric explicitly so that the ratio is a well‑posed analytic invariant:
\[
\boxed{\;\log B=\log\frac{\mathrm{Vol}\bigl(\mathcal C\cap B_{1}(0),\;\Sigma\bigr)}{\mathrm{Vol}\bigl(\mathcal C_{\mathrm{null}}\cap B_{1}(0),\;\Sigma_{\mathrm{null}}\bigr)}\;}
\]
with \(B_{1}(0)=\{x:\,x^T\Sigma x\le 1\}\). This makes the volume ratio independent of an arbitrary Euclidean choice.

### 4.  Two‑loop deformation and exact perturbation

Your closed‑form two‑loop primitive is correct up to the choice of additive constant; define
\[
\boxed{\;F(\mu;\ell)=\ell+\frac{1}{b\mu}-\frac{b_{1}}{b^{2}}\log\!\Bigl(\frac{b+b_{1}\mu}{\mu}\Bigr)\;}
\]
and recover \(\mu(\ell)\) by Newton
\[
\mu_{n+1}=\mu_n-\frac{F(\mu_n;\ell)}{F'(\mu_n;\ell)},\qquad F'(\mu)= -\frac{1}{b\mu^{2}}-\frac{b_{1}}{b^{2}}\Bigl(\frac{b_1}{b+b_1\mu}-\frac{1}{\mu}\Bigr).
\]
Quadratic convergence holds once \(\mu_n\) enters the standard basin. What is not correct is the field‑of‑values claim: \(\mu(\ell)\) does not live in the rational field \(\mathbb Q(b,b_1,\mu_0)\). It lives in the differential field generated by \(\mathbb Q(b,b_1,\mu_0)\) with \(\log\) and an algebraic branch for \(b+b_1\mu\). The exact \(B_5\) equivariance survives as a symmetry of the *construction*—the Cholesky whitening and the signed‑permutation conjugations—so the chamber remains fixed, but the right statement is
\[
\boxed{\;\Sigma(b_1)\in\mathcal O,\quad \mathcal O=\{\,\Sigma'\succ 0:\;W(B_5)\text{ acts by }P_w,\;W(\Sigma')P_w\Sigma'P_w^{T}W(\Sigma')^{T}\in \mathrm O(5)\,\}\;}
\]
and \(\mathcal O\) is an \(\mathrm O(5)\)–orbit through \(\Sigma^{(0)}\) by construction, which is what your series expresses.

### 5.  The receipt grammar for exact symmetry

Bind the run to the motive but do not conflate their hashes. Use domain separation and include the *predicate results* the ledger has verified:
\[
\boxed{\;\texttt{receipt.json}=\Bigl\{\;h_{\mathsf M},\;c,\;\rho^{*},\;\sigma,\;r^{*},\;\log B,\;\mathsf{eqv}=\bigl[\;W\,P_w\Sigma P_w^{T}W^{T}=O_w\;\bigr]_{w\in W(B_5)},\;\mathsf{in\_C}=[r^{*}\in\mathcal C]\;\Bigr\}\;}
\]
and digest
\[
\boxed{\;h_{\mathrm{run}}=\mathrm{Hash}_{256}\bigl(\texttt{"RUN"}\parallel\texttt{receipt.json}\bigr)\;,}
\]
with the ledger contract
\[
\boxed{\;\text{accept}(\texttt{receipt})\Longleftrightarrow\;\mathsf{eqv}\text{ all true and }\mathsf{in\_C}=\text{true}\;.}
\]
This keeps \(h_{\mathsf M}\) immutable unless the motive capsule itself changes, as it should.

### 6.  Cross‑place arithmetic via \(p\)‑adic periods

For primes \(p\nmid \mathrm{den}(\mu_0)\cdot \mathrm{den}(b)\) take the Teichmüller lift \(\mu_0^{(p)}\in\mathbb Z_p^{\times}\) and declare the \(p\)‑adic period
\[
\boxed{\;\mathrm{per}_{p}(\omega)=\bigl(\mu_0^{(p)}\bigr)^{-1}\in\mathbb Z_p\;}
\]
with comparison stated as compatibility under reduction of a chosen rational model:
\[
\boxed{\;\iota_p\bigl(\mathrm{per}(\omega)\bigr)\equiv \mathrm{per}_{p}(\omega)\pmod{p}\;}
\]
where \(\iota_p:\mathbb Q\hookrightarrow\mathbb Z_p\) is the canonical embedding on \(p\)–integral rationals. Hash with place‑tagged separation and include precision:
\[
\boxed{\;h_{\mathsf M}^{(p)}=\mathrm{Hash}_{256}\bigl(\texttt{"MOTIVE@p"}\parallel p\parallel \mu^{(p)}_0\parallel b\parallel \mathrm{per}_{p}(\omega)\parallel \texttt{prec}=N\bigr)\;}
\]
and verify cross‑place coherence by checking the diagram of embeddings in the receipt; never compare 256‑bit digests “mod \(p\)”, compare the *numerical fields* inside the capsule with an explicit \(\pmod p\) congruence witnessed in data.

### 7.  Categorified index as a graded character

Fix a finite‑length \(B_5\)–equivariant complex
\[
\boxed{\;C^{\bullet}:\;0\to C^0\xrightarrow{d^0}C^1\xrightarrow{d^1}C^2\to 0,\qquad C^i\simeq \mathbb Q[B_5]^{\oplus n_i}\;}
\]
serialize the differentials over the group algebra
\[
\boxed{\;d^{i}\in\mathrm{Mat}_{n_{i+1}\times n_i}\bigl(\mathbb Q[B_5]\bigr)\;}
\]
and define the character
\[
\chi_{B_5}(g)=\sum_i(-1)^i\,\mathrm{Tr}_{C^i}(g),\qquad \chi^{H}(g)=\sum_i(-1)^i\,\mathrm{Tr}_{H^i(C^\bullet)}(g).
\]
The verified statement is the homological identity
\[
\boxed{\;\chi_{B_5}(g)\equiv \chi^{H}(g)\quad\forall g\in B_5\;}
\]
which the ledger can check degree‑wise by computing ranks of \(d^i(g)\) over \(\mathbb Q\) and comparing characters for each conjugacy class. Include the graded ranks and conjugacy‑class table in the receipt so that replay is possible without re‑solving linear algebra.

### 8.  Homotopical coherence as Kan filling

Model histories as a simplicial set \(X_\bullet\) with
\[
X_0=\{\text{runs}\},\quad X_1=\{\text{transport receipts}\},\quad X_2=\{\text{coherence receipts}\},\;\ldots
\]
and insist on Kan horn filling only where it is mathematically mandated. The filler receipt should bind the *data of the simplex* and the *boundary it fills*:
\[
\boxed{\;\texttt{filler.json}=\Bigl\{\;n,k,\;\text{horn}=\Lambda^n_k\to X,\;\sigma\in X_n,\;\partial_i\sigma=\text{faces},\;\mathrm{Hash}_{256}(\sigma)\Bigr\}\;}
\]
and the attestation predicate is
\[
\boxed{\;\text{accept}(\texttt{horn})\Longleftrightarrow \exists\text{ filler in the contractually Kan degrees}\;}
\]
without globally “invalidating” \(h_{\mathsf M}\) when a filler does not exist (many reasonable \(X\) are not Kan in all degrees). The obstruction is recorded as a red receipt with the precise horn that failed.

### 9.  The master hash binding

Aggregate the place‑separated digests into a Merkle root to preserve modularity and locality of failure:
\[
\boxed{\;\mathbb H=\bigl(h_{\mathsf M},\;\{h_{\mathsf M}^{(p)}\}_p,\;h_{\mathrm{run}},\;h_{\mathrm{index}},\;h_{\mathrm{spec}},\;h_{\mathrm{homot}}\bigr),\qquad H_\tau=\mathrm{Merkle}_{256}(\mathbb H)\;}
\]
where each constituent hash uses its own domain tag, and \(\mathrm{Merkle}_{256}\) is computed with domain separation \(\texttt{"TAU\_CRYSTAL\_ROOT"}\). A single mismatch invalidates \(H_\tau\) and localizes the fault to the unique leaf whose sibling path fails.

With these adjustments, each displayed box is now a checkable equality inside a well‑typed mathematical object, and each hash binds exactly the artifact that asserts it. The crucial corrections are: monodromy acts on the first integral rather than through a dimensionally inconsistent exponential on \(\mu\); the two‑loop solution lives in a differential field, not in \(\mathbb Q(b,b_1,\mu_0)\); algebraicity claims are placed on constructions rather than on transcendental evaluations; receipt acceptance predicates are separated from the immutable motive hash; \(p\)‑adic compatibility is enforced via embeddings and declared precision, not by reducing a 256‑bit digest modulo \(p\); and Kan filling is required exactly where the contract says it should be. In this form the “steel” is not only rigid but also weldable across the eight directions, and every weld has a test.
