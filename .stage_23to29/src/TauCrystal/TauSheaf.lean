import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Opposites

open CategoryTheory
namespace TauCrystal
universe u

-- ASCII-only: use Opposite C instead of Cᵒᵖ to avoid UTF-8 issues
variable {C : Type u} [Category C]
variable (J : GrothendieckTopology (Opposite C))

/- TauCapsule: convergence metadata (tail L1, rho, epsilon for dH bound) -/
structure TauCapsule where
  tailL1 : Real
  rho    : Real
  eps    : Real

/- TauSheaf := base site-theoretic sheaf + capsule metadata -/
structure TauSheaf (J : GrothendieckTopology (Opposite C)) (C : Type u) [Category C] where
  base : Sheaf J C
  meta : TauCapsule

def tauFixpoint (S : TauSheaf J C) : Prop :=
  S.meta.tailL1 < (1e-6) ∧ S.meta.rho < 1 ∧ 0 ≤ S.meta.eps

end TauCrystal
