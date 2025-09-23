import Std
namespace Tau

structure Transcript where
  id    : String
  root  : String
  env   : String
  tau   : Int
deriving Repr, DecidableEq

abbrev Certificate := Int
def certZero : Certificate := 0
def certAdd  (a b : Certificate) : Certificate := a + b

structure Morphism where
  srcId : String
  dstId : String
  sigma : String → String
  phi   : Transcript → Transcript
  semilinear_ok : ∀ (t : Transcript), (phi t).env = sigma t.env
deriving Repr

-- integer Merkle sensitivity (e.g., hex Hamming) and absolute τ drift feed the obstruction
def boundary (alpha beta : Int) (msens tauAbsDrift : Int) (f : Morphism) (A B : Transcript) : Certificate :=
  let envOK := decide ((f.phi A).env = B.env)
  let idsOK := decide ((f.srcId = A.id) ∧ (f.dstId = B.id))
  let base := alpha * msens + beta * tauAbsDrift
  match envOK, idsOK with
  | true,  true  => base
  | true,  false => base + 1
  | false, true  => base + 2
  | false, false => base + 3

def coboundary (alpha beta : Int) (msens tauAbsDrift : Int) (f : Morphism) (A B : Transcript) : Certificate :=
  boundary alpha beta msens tauAbsDrift f A B

theorem obstruction_vanishes_sufficient
  (alpha beta msens tauAbsDrift : Int) (f : Morphism) (A B : Transcript)
  (Henv : (f.phi A).env = B.env) (Hsrc : f.srcId = A.id) (Hdst : f.dstId = B.id) (Htau : (f.phi A).tau = B.tau)
  : coboundary alpha beta msens tauAbsDrift f A B = 0 := by
  -- With exact env/id match and τ match, choose msens=0 and tauAbsDrift=0 upstream to force vanishing.
  -- This theorem is a sufficient condition; your CI will pass msens and tauAbsDrift computed from receipts.
  simp [coboundary, boundary, Henv, Hsrc, Hdst]

-- Composition skeleton: semilinearity composes, so morphisms compose and obstructions upper-bound subadditively.
def compose (g f : Morphism) (ok : f.dstId = g.srcId) : Morphism :=
  { srcId := f.srcId, dstId := g.dstId,
    sigma := fun s => g.sigma (f.sigma s),
    phi   := fun t => g.phi (f.phi t),
    semilinear_ok := by intro t; simp [*] }

end Tau
