/-
  HEO — Core formalization (Tier 0–2 skeleton)
  Uses mathlib4 for ℝ, filters, limsup, Finset, etc.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Set.Finite
import Mathlib.Order.Filter.AtTopBot

open Classical

namespace HEO

/-- Integer-valued sequence -/
abbrev Sequence := ℕ → ℤ

/-- Indicator of a d-th power hit: 1 if ∃ m, S n + k = m^d, else 0 (as ℕ). -/
noncomputable def X (S : Sequence) (d : ℕ) (k : ℤ) (n : ℕ) : ℕ :=
  if ∃ m : ℤ, S n + k = m ^ d then 1 else 0

/-- X is binary (0 or 1). -/
lemma X_binary (S : Sequence) (d : ℕ) (k : ℤ) (n : ℕ) :
    X S d k n = 0 ∨ X S d k n = 1 := by
  unfold X; by_cases h : ∃ m : ℤ, S n + k = m ^ d <;> simp [h]

/-- Partial sums up to N (exclusive of 0, inclusive of N). -/
def partialSum (S : Sequence) (d : ℕ) (k : ℤ) (N : ℕ) : ℕ :=
  (Finset.range N).sum (fun i => X S d k (i + 1))

/-- Cesàro density at N as ℝ. -/
noncomputable def density (S : Sequence) (d : ℕ) (k : ℤ) (N : ℕ) : ℝ :=
  if hN : 0 < N then (partialSum S d k N : ℝ) / (N : ℝ) else 0

/-- HEO as limsup of densities. -/
noncomputable def H (S : Sequence) (d : ℕ) (k : ℤ) : ℝ :=
  Filter.limsup (fun N : ℕ => density S d k N) Filter.atTop

/-- Trivial bounds: 0 ≤ density ≤ 1. -/
lemma density_bounds (S : Sequence) (d : ℕ) (k : ℤ) (N : ℕ) :
    0 ≤ density S d k N ∧ density S d k N ≤ 1 := by
  classical
  by_cases hN : 0 < N
  · have posN : (0 : ℝ) < N := by exact_mod_cast hN
    have h0 : (0 : ℝ) ≤ (partialSum S d k N : ℝ) := by exact_mod_cast Nat.zero_le _
    have hx : partialSum S d k N ≤ N := by
      unfold partialSum
      refine (Finset.sum_le_card_nsmul (s := fun i => X S d k (i+1)) ?h ?g).trans ?t
      · intro i _
        rcases X_binary S d k (i+1) with h0 | h1
        · simpa [h0]
        · simpa [h1]
      · simp
      · simp
    constructor
    · have : 0 ≤ (partialSum S d k N : ℝ) / N := by
        exact div_nonneg h0 (le_of_lt posN)
      simpa [density, hN] using this
    · have : (partialSum S d k N : ℝ) / N ≤ 1 := by
        have : (partialSum S d k N : ℝ) ≤ N := by exact_mod_cast hx
        exact (div_le_one_of_le this posN)
      simpa [density, hN] using this
  · simp [density, hN]

/-- Theorem (Tier 0): finite solution set ⇒ H = 0. -/
theorem finite_implies_zero
  (S : Sequence) (d : ℕ) (k : ℤ)
  (hfin : Set.Finite {n : ℕ | X S d k n = 1}) :
  H S d k = 0 := by
  classical
  /- Sketch: partialSum ≤ C ⇒ density ≤ C/N ⇒ limsup = 0. -/
  sorry

/-- Theorem (Tier 0): finite surgery invariance. -/
theorem finite_surgery_invariance
  (S S : Sequence) (d : ℕ) (k : ℤ)
  (N₀ : ℕ)
  (agree_tail : ∀ n ≥ N₀, S n = S n) :
  H S d k = H S d k := by
  classical
  /- Densities differ by O(1/N) from finite prefix; limsup equal. -/
  sorry

/-- Theorem (Tier 9 exact model): periodic indicator ⇒ rational density. -/
theorem periodic_rationality
  (S : Sequence) (d : ℕ) (k : ℤ)
  (T : ℕ) (hT : 0 < T)
  (pattern : Fin T → ℕ) (h01 : ∀ i, pattern i = 0 ∨ pattern i = 1)
  (hXper : ∀ n, X S d k (n+1) = pattern ⟨n % T, by
      have := Nat.mod_lt n (Nat.succ_le_of_lt hT); simpa using this⟩) :
  ∃ q : ℚ, H S d k = q := by
  classical
  /- Cesàro limit equals average over one period. -/
  sorry

end HEO
