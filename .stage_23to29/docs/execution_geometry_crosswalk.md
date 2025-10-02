# Explorer ↔ Seifert ↔ Execution Geometry (Capsule Crosswalk)

**Arithmetic skeleton.** Let \(p\) be prime, \(b\) a base with \(\gcd(b,p)=1\). The multiplicative order \(d=\mathrm{ord}_p(b)\) acts on the repetend \(R_p\) as the cyclic group \(C_d\). A primitive root \(g\in\mathbb{F}_p^\times\) witnesses \(\mathbb{F}_p^\times=\langle g\rangle\). The Explorer’s rotation step \(k\mapsto \rho_k\) is the character \(C_d\to \mathrm{SO}(2)\), \(1\mapsto e^{2\pi i/d}\).

**Topological skeleton.** A Seifert fiber space is a circle bundle \(S^1\hookrightarrow M\stackrel{\pi}{\to}B\) over an orbifold \(B\) with normalized symbol \(\{b,(\varepsilon,g);(a_1,b_1),\dots,(a_r,b_r)\}\), orbifold Euler characteristic \(\chi(B)=\chi(B_0)-\sum_{i=1}^r (1-1/a_i)\), and oriented Euler class \(e=b+\sum b_i/a_i\in\mathbb{Q}\).

**Identification.** After the \(A=\mathrm{lcm}(a_i)\) cover of \(B\), every exceptional angle \(2\pi b_i/a_i\) becomes an integer multiple of \(2\pi/A\). If \(d\mid A\), there is a bookkeeping isomorphism sending one Explorer digit‑step to \(2\pi/d\) so the Seifert holonomy factors through \(C_d\). The Euler class becomes a rational winding number measured by the Explorer’s clock. Signs of \(\chi(B)\) select the Thurston regime; when \(\chi(B)=0\) the split flag \(e=0\) distinguishes EUCLIDEAN from NIL.

**Capsule record.** The gate records:
\[
\texttt{prime\_p},\ \texttt{base\_b},\ \texttt{ord\_d},\ \texttt{pairs}=(a_i,b_i),\ A=\mathrm{lcm}(a_i),\ e=\frac{\texttt{numer}}{\texttt{denom}},\ \texttt{divides}=(d\mid A),\ \texttt{cover\_index}=A/d,\ \texttt{regime}.
\]
This is sufficient to re‑establish alignment without replaying the UI.
