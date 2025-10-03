import Mathlib
import HEO.Core
import HEO.Notation
set_option autoImplicit true

namespace HEO
open Classical

/-!
  Module: Analytical
  Operator: identity (f x = x)
  Density predicate: P n := n % 2 = 0, witness δ = 1/2.
-/

def ModuleContract : HEO.Contract Real Real Real :=
  contractOf
    (dom := fun _ => True)
    (cod := fun _ => True)
    (f := id)
    (hlin := by intro x y _ _; simp)
    (res := (0.0 : Real))
    (P := fun n => n % 2 = 0)
    (delta := (1 : Real) / (2 : Real))

theorem Analytical_linear_check :
  ModuleContract.T.toFun (1 + 2)
    = ModuleContract.T.toFun 1 + ModuleContract.T.toFun 2 := by
  have hx : ModuleContract.T.dom (1 : Real) := trivial
  have hy : ModuleContract.T.dom (2 : Real) := trivial
  simpa using HEO.linear_add ModuleContract.T (x:=(1:Real)) (y:=(2:Real)) hx hy

@[simp] theorem Analytical_f_three :
  ModuleContract.T.toFun (3 : Real) = 3 := by simp

end HEO
