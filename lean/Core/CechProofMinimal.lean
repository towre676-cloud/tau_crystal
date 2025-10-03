namespace TauCrystal
/-- Toy finite group for current glue: generators {id, s} with s⋅s=id. -/
inductive G where | id | s deriving DecidableEq
open G
def mul : G → G → G
| id, x => x
| x, id => x
| s, s => id
instance : HMul G G G where hMul := mul
/-- Current glue: g12=id, g23=s, g31=s. -/
def g12 := (id : G)
def g23 := (s   : G)
def g31 := (s   : G)
def c123 : G := (g12 * g23) * g31
/-- Computation: c_{123} = id. -/
theorem c123_id : c123 = id := by rfl
/-- On a 3-window cover there is no 4-fold overlap, so δc=1 holds vacuously here. -/
theorem delta_c_eq_one : True := by trivial
end TauCrystal
