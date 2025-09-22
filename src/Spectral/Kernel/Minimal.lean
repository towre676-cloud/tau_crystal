namespace Spectral.Kernel

/-- Minimal Box + Edge types the demos expect. -/
structure Box where
  label   : String
  framing : Int
  p       : Int
  heegner : Int × Int × Int
  deriving Repr, DecidableEq

structure Edge where
  src    : Box
  dst    : Box
  weight : Int
  deriving Repr, DecidableEq

/-- Plumbing container to match `{ vertices := …, edges := … }` usage. -/
structure Plumbing where
  vertices : List Box
  edges    : List Edge
  deriving Repr, DecidableEq

/-- Very simple stand-ins for invariants. Tune later. -/
def tamagawa (_Δ : Int) (p : Int) : Nat :=
  if p % 2 == 0 then 0 else 1

def boxMaslov (b : Box) : Int :=
  if b.framing % 2 == 0 then 0 else 1

def globalMaslov (pl : Plumbing) : Int :=
  (pl.vertices.map boxMaslov).foldl (· + ·) 0

/-- JSON helpers. -/
private def esc (s : String) : String :=
  -- Minimal: enough for current labels; extend if you need more escaping.
  s.replace "\"" "\\\""

def emitNode (b : Box) (_Δ : Int) : String :=
  s!"{{\"label\":\"{esc b.label}\",\"maslov\":{boxMaslov b},\"tamagawa\":{tamagawa 0 b.p}}}"

def emitEdge (e : Edge) : String :=
  s!"{{\"from\":\"{esc e.src.label}\",\"to\":\"{esc e.dst.label}\",\"int\":{e.weight}}}"

def emitPlumbingTrace (Δ : Int) (pl : Plumbing) : String :=
  let nodes := pl.vertices.map (fun v => emitNode v Δ)
  let edges := pl.edges.map emitEdge
  s!"{{\"nodes\":[{String.intercalate "," nodes}],\"edges\":[{String.intercalate "," edges}]}}"

end Spectral.Kernel
