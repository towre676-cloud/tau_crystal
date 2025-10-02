# Execution Geometry of Seifert‑Fibered CI\n
_A τ‑Crystal monograph binding Seifert classification to crash‑proof, cover‑trivial continuous integration._\n
## Abstract\n
We formalize execution as a Seifert fibration: time is the regular circle fiber and the code base modulo time is the 2‑orbifold base. Ordinary fibers are side‑effect‑free τ‑ticks; exceptional fibers encode rational holonomy from nondeterminism, API aliasing, or numerical and scheduler effects. The Seifert symbol \(\{b,(\varepsilon,g);(a_1,b_1),\dots,(a_r,b_r)\}\) becomes a canonical execution type. From it we compute the orbifold Euler characteristic \(\chi(B)\), the e‑invariant \(e=b+\sum b_i/a_i\), and the period \(L=\mathrm{lcm}(a_i)\). Policy is then curvature‑driven: \(\chi(B)>0\) demands a finite‑state certificate; \(\chi(B)=0\) abelianizes to Euclidean or nil; \(\chi(B)<0\) is uniquely fibered and intrinsically crash‑resistant. The group relations become receipt grammar, making debugging a topological impossibility: either relations close and the run is admitted, or they do not and the run is refused before execution.\n
## Dictionary\n
| Seifert object | Execution meaning | CI effect |\n
|---|---|---|\n
| Fiber \(S^1\), generator \(h\) | τ‑clocked loop | Central tick, receipt cadence |\n
| Base orbifold \(B\) | Program world modulo time | DAG semantics without wall‑clock |\n
| Exceptional \((a,b)\) | Rational holonomy site | Quantized retries, rounding, cache epochs |\n
| \(e=b+\sum b_i/a_i\) | Cover‑triviality index | \(e=0\) ⇔ period‑L cover untwists to product |\n
| \(\chi(B)\) | Curvature of execution | Governs geometry class and guard policy |\n
## Normalization and Surgery\n
Refactors that preserve semantics are precisely Seifert normalization moves: sliding global debt \(b\) into local \(b_i\), adding \((1,0)\) no‑ops, and, in non‑orientable loci, sign changes corresponding to permitted time reversals. Surgery adds or removes exceptional sites with explicit holonomy contracts; receipt‑wise this is an auditable change of symbol that preserves or lowers \(\chi\) and maintains centrality of \(h\).\n
## Group Grammar as Receipt Law\n
The relations \(q_j^{a_j}h^{b_j}=1\) and the global closure to \(h^{b}\) define the only admissible step completions. Each step that touches a holonomy site must declare the pair \((a_j,b_j)\) and discharge it into τ. A pipeline that cannot spell its run as a product of these relations has no fibration and is rejected. This replaces debugging with algebraic closure.\n
## Curvature Policy\n
Positive \(\chi\) requires a finite‑state certificate because execution is virtually cyclic or finite; without it, the system can fold into brittle lens‑like pockets. Zero \(\chi\) splits into Euclidean with \(e=0\) and nil with \(e\neq 0\); the former commutes strictly under a period‑\(L\) cover, the latter is a central extension that must be attested. Negative \(\chi\) is aspherical: the fibration is unique up to isomorphism and higher homotopy vanishes, eliminating ghost cycles.\n
## Algorithms\n
Collapse the CI DAG along τ to obtain \(B\) and enumerate exceptional sites. Compute \(\chi(B_0)=2-2g\) for orientable base or \(2-g\) for non‑orientable. Subtract \(\sum(1-1/a_i)\) to obtain \(\chi(B)\). Compute \(e\) and \(L\). Emit a report, hash it, and link as the latest ledger object. The guard enforces: finite‑state proof if \(\chi>0\); acceptance for \(\chi<0\); abelianization checks in the \(\chi=0\) zone, with \(e=0\) enabling strict cover runs.\n
## Implementation Notes\n
All scripts are Bash‑only and heredoc‑free. Configuration lives in .exec_geom/symbol.conf and .exec_geom/exceptionals.tsv. The calculator writes .tau_ledger/exec_geom/latest.json with invariants, geometry class, L, and SHA‑256. The guard integrates into CI and returns nonzero on policy violation, making curvature a first‑class gate.\n
## Operational Law\n
Time is central, holonomy is declared, curvature is enforced. When those three are true, the CI ceases to be a source of bugs because it becomes a fibration with a unique closure; when any fails, we refuse to run. This is not a metaphor but a topology for execution that the ledger proves on every pass.\n
