import Mathlib
import HEO.Core
import HEO.Notation
set_option autoImplicit true

namespace HEO
open Classical

/-!
  Module: Combinatorial
  Operator: f x = 12 • x
  Density predicate: P n := n % 14 = 0, witness δ = 1/14.
-/

def ModuleContract : HEO.Contract Real Real Real :=
  contractOf
    (dom := fun _ => True)
    (cod := fun _ => True)
    (f := fun x => 12 • x)
    (hlin := by intro x y _ _; simpa [nsmul_add])
    (res := (0.0 : Real))
    (P := fun n => n % 5 = 0)
    (delta := (1 : Real) / (5 : Real))

theorem Combinatorial_linear_check :
  ModuleContract.T.toFun (1 + 2) =
    ModuleContract.T.toFun 1 + ModuleContract.T.toFun 2 := by
  have hx : ModuleContract.T.dom (1 : Real) := trivial
  have hy : ModuleContract.T.dom (2 : Real) := trivial
  simpa using HEO.linear_add ModuleContract.T (x:=(1:Real)) (y:=(2:Real)) hx hy

@[simp] theorem Combinatorial_f_three :
  ModuleContract.T.toFun (3 : Real) = 12 • (3 : Real) := by
  simp [nsmul_add]

end HEO
