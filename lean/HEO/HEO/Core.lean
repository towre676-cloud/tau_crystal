import Mathlib
set_option autoImplicit true
set_option warningAsError false
set_option linter.dupNamespace false

namespace HEO
open Classical

/- Bundled Harmonic Effectiveness Operator with additive structure. ASCII-safe. -/
structure Op (A B : Type _) [Add A] [Add B] where
  dom   : A -> Prop
  cod   : B -> Prop
  toFun : A -> B
  linear : forall {x y : A}, dom x -> dom y -> toFun (x + y) = toFun x + toFun y

/- Safe application gated by the declared domain. Needs classical decidability. -/
noncomputable def apply {A B} [Add A] [Add B] (T : Op A B) (x : A) : Option B :=
  if h : T.dom x then some (T.toFun x) else none

/- Axiomatized residue carrier hooked to receipts later. -/
class Residue (G : Type _) where
  R : G -> Real

/- Asymptotic density witness hook. -/
structure DensityWitness where
  P     : Nat -> Prop
  value : Real
  isLimsupBound : Prop

/- Minimal per-module interface: operator, residue carrier, and density witness. -/
structure Contract (A B G : Type _) [Add A] [Add B] where
  T    : Op A B
  C    : G
  inst : Residue G
  Delta : DensityWitness

/- Canonical linearity lemma for simp. -/
theorem linear_add {A B} [Add A] [Add B]
  (T : Op A B) {x y : A} (hx : T.dom x) (hy : T.dom y) :
  T.toFun (x + y) = T.toFun x + T.toFun y := by
  simpa using T.linear (x:=x) (y:=y) hx hy

/- Harmless default residue instance for Real so modules compile before proofs. -/
instance : Residue Real where
  R := id

end HEO
