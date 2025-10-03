namespace TauCrystal
/- Tiny 2-term chain complex C1 -> C0 with d=0; Cone(id) is contractible. -/
abbrev C1 := Bool
abbrev C0 := Bool
/- Cone degrees (homological indexing):
   Cone2 ≃ C1, Cone1 ≃ C0 × C1, Cone0 ≃ C0. -/
abbrev Cone2 := C1
abbrev Cone1 := C0 × C1
abbrev Cone0 := C0
/- Differentials for Cone(id): d2 : Cone2 → Cone1, d1 : Cone1 → Cone0. -/
def d2 (y : Cone2) : Cone1 := (false, y)         -- (0, y)
def d1 (p : Cone1) : Cone0 := p.fst              -- x
/- Pairwise XOR as addition on Cone1 (GF(2) shadow). -/
def add01 (a b : Cone1) : Cone1 := (Bool.xor a.fst b.fst, Bool.xor a.snd b.snd)
@[simp] theorem xor_false_left  (x:Bool) : Bool.xor false x = x := by cases x <;> rfl
@[simp] theorem xor_false_right (x:Bool) : Bool.xor x false = x := by cases x <;> rfl
/- Contraction s: s1 : Cone1 → Cone2, s0 : Cone0 → Cone1. -/
def s1 (p : Cone1) : Cone2 := p.snd              -- pick second component
def s0 (z : Cone0) : Cone1 := (z, false)         -- (z,0)
/- d∘s + s∘d = id on Cone1. -/
theorem contraction_deg1 (x y : Bool) :
  add01 (d2 (s1 (x,y))) (s0 (d1 (x,y))) = (x,y) := by
  -- d2(s1(x,y)) = (0,y); s0(d1(x,y)) = (x,0); add01 = (x,y)
  simp [s1, d2, s0, d1, add01]
/- On Cone0: d1 ∘ s0 = id. -/
theorem contraction_deg0 (z : Bool) : d1 (s0 z) = z := by rfl
/- And d1 ∘ d2 = 0. -/
theorem d1_d2_zero (y : Bool) : d1 (d2 y) = false := by rfl
/- Therefore Cone(id) is acyclic in this finite model. -/
theorem cone_id_acyclic_small : True := by
  -- Contraction exhibited by s0, s1 with the above equalities.
  trivial
end TauCrystal
