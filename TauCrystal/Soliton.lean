namespace TauCrystal

/-- Primitive proof/build steps kept intentionally small. -/
inductive Step
| fetchMathlib : String → Step
| compileModule : Name → Step
| checkTheorem : Name → Step
| runTactic : Name → Step
deriving DecidableEq, Repr

structure Transport where
  kernel    : String
  glibc     : String
  toolchain : String
  hostname  : String
deriving Repr, DecidableEq

structure Event where
  step      : Step
  transport : Transport
  stamp     : Nat
deriving Repr, DecidableEq

abbrev Trace := List Event

def semantics (tr : Trace) : List Step := tr.map (·.step)

def normalize : Trace → List Step
| []        => []
| e :: rest => e.step :: normalize rest

def Soliton := List Step

def toSoliton (tr : Trace) : Soliton := normalize tr

structure Residue where
  missing   : List Step
  surplus   : List Step
  permError : Bool
deriving Repr, DecidableEq

def residue (target : Soliton) (tr : Trace) : Residue :=
  let want := target
  let have := normalize tr
  let missing := want.filter (fun s => ¬ have.contains s)
  let surplus := have.filter (fun s => ¬ want.contains s)
  let perm := (want ≠ have) && (missing.isEmpty ∧ surplus.isEmpty)
  { missing := missing, surplus := surplus, permError := perm }

/-- Two traces are "admissible" if they have the same semantic spine (steps), ignoring transport. -/
def Admissible (tr₁ tr₂ : Trace) : Prop := semantics tr₁ = semantics tr₂

/-- Helper: with our definitions, `normalize` equals `semantics`. -/
theorem normalize_eq_semantics : ∀ (tr : Trace), normalize tr = semantics tr := by
  intro tr; induction tr with
  | nil => simp [normalize, semantics]
  | cons e rest ih =>
      cases e with
      | mk step transport stamp =>
        simp [normalize, semantics, ih]

/-- Soliton conservation: admissible transports preserve the soliton class. -/
theorem soliton_conserved {tr₁ tr₂ : Trace} (H : Admissible tr₁ tr₂) :
  toSoliton tr₁ = toSoliton tr₂ := by
  unfold Admissible toSoliton at *
  have h1 := normalize_eq_semantics tr₁
  have h2 := normalize_eq_semantics tr₂
  -- rewrite both sides to `semantics`
  simpa [h1, h2] using congrArg id H

end TauCrystal
