import Mathlib
import HEO.Core
set_option autoImplicit true

namespace HEO
open Classical

def contractOf
  {A B G} [Add A] [Add B]
  (dom : A -> Prop) (cod : B -> Prop) (f : A -> B)
  (hlin : forall x y, dom x -> dom y -> f (x + y) = f x + f y)
  (res : G) [Residue G]
  (P : Nat -> Prop) (delta : Real) (isSup : Prop := True) :
  HEO.Contract A B G :=
  let T : HEO.Op A B := {
    dom := dom, cod := cod, toFun := f,
    linear := by intro x y hx hy; exact hlin x y hx hy
  }
  { T := T, C := res, inst := inferInstance,
    Delta := { P := P, value := delta, isLimsupBound := isSup } }

end HEO
