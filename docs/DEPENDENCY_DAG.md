# Dependency DAG (prose graph of the executed theory)

The graph encodes leaf probes → constructors → functorial gluing → apex point value **E**. Edges are typed by creation of receipts, boundary pushforwards, restriction and descent, and curvature accounting.

```mermaid
flowchart TD
  subgraph Leaves[Leaf Probes]
    A1[FFT derivative estimators]\nA2[Chebyshev decay samplers]\nA3[Hecke counters]\nA4[q‑Euler factor extractors]
  end
  subgraph Constructors[Constructors]
    C1[ResidueComplex (log‑det curvature)]\nC2[τ‑pulse aggregator]\nC3[Certificate grammar]\nC4[Receipt restriction maps]
  end
  subgraph Functorial[Functorial Layer]
    F1[assure.sh composition (bordisms)]\nF2[Replay equivalences (2‑morphisms)]\nF3[Anomaly budget integrator]
  end
  subgraph Apex[Point Value]
    E[Epistemic Module **E**\n(det line + Quillen, factorization over τ, spectral triple)]
  end
  A1 -->|creates micro‑receipt| C1
  A2 -->|creates micro‑receipt| C2
  A3 -->|coefficients| C3
  A4 -->|period samples| C1
  C1 -->|curvature 2‑form| F3
  C2 -->|τ‑coordinate| F1
  C3 -->|typed boundaries| F1
  C4 -->|descent data| F1
  F1 -->|monoidal composition| E
  F2 -->|higher coherence| E
  F3 -->|holonomy budget| E
```
