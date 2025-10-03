import Mathlib
import HEO.Core
import HEO.Notation
set_option autoImplicit true

namespace HEO
open Classical

/-!
  Module: Geometric
  Operator: f x = 13 • x
  Density predicate: P n := n % 15 = 0, witness δ = 1/15.
-/

def ModuleContract : HEO.Contract Real Real Real :=
  contractOf
    (dom := fun _ => True)
    (cod := fun _ => True)
    (f := fun x => 13 • x)
    (hlin := by intro x y _ _; simpa [nsmul_add])
    (res := (0.0 : Real))
    (P := fun n => n % 4 = 0)
    (delta := (1 : Real) / (4 : Real))

theorem Geometric_linear_check :
  ModuleContract.T.toFun (1 + 2) =
    ModuleContract.T.toFun 1 + ModuleContract.T.toFun 2 := by
  have hx : ModuleContract.T.dom (1 : Real) := trivial
  have hy : ModuleContract.T.dom (2 : Real) := trivial
  simpa using HEO.linear_add ModuleContract.T (x:=(1:Real)) (y:=(2:Real)) hx hy

@[simp] theorem Geometric_f_three :
  ModuleContract.T.toFun (3 : Real) = 13 • (3 : Real) := by
  simp [nsmul_add]

end HEO
