/-
  HEO — Core formalization (Tier 0–2 skeleton)
  Uses mathlib4 for ℝ, filters, limsup, Finset, etc.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Topology.Algebra.InfiniteSum
import Mathlib.Topology.Algebra.Order
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Set.Finite
import Mathlib.MeasureTheory/Measure/MeasureSpace

namespace HEO

/-- Integer-valued sequence -/
abbrev Sequence := ℕ → ℤ

/-- Indicator of a d-th power hit: 1 if ∃ m, S n + k = m^d, else 0 (as ℕ). -/
def X (S : Sequence) (d : ℕ) (k : ℤ) (n : ℕ) : ℕ :=
  if h : ∃ m : ℤ, S n + k = m ^ d then 1 else 0

/-- Partial sums up to N (exclusive of 0, inclusive of N). -/
def partialSum (S : Sequence) (d : ℕ) (k : ℤ) (N : ℕ) : ℕ :=
  (Finset.range N).sum (fun i => X S d k (i+1))

/-- Cesàro density at N as ℝ. -/
def density (S : Sequence) (d : ℕ) (k : ℤ) (N : ℕ) : ℝ :=
  if hN : 0 < N then (partialSum S d k N : ℝ) / (N : ℝ) else 0

/-- HEO as limsup of densities. -/
noncomputable def H (S : Sequence) (d : ℕ) (k : ℤ) : ℝ :=
  Filter.limsup (fun N : ℕ => density S d k N) Filter.atTop

/-- Trivial bounds: 0 ≤ density ≤ 1. -/
lemma density_bounds (S : Sequence) (d : ℕ) (k : ℤ) (N : ℕ) :
    0 ≤ density S d k N ∧ density S d k N ≤ 1 := by
  by_cases hN : 0 < N
  ·
    have h0 : (0 : ℝ) ≤ (partialSum S d k N : ℝ) := by exact_mod_cast Nat.zero_le _
    have h1 : (partialSum S d k N : ℝ) ≤ N := by
      -- each term ≤ 1
      have : partialSum S d k N ≤ N := by
        refine (Finset.sum_le_card_nsmul _ ?_ ?_).trans ?_
        · intro i hi
          by_cases h : X S d k (i+1) = 1
          · simpa [h]
          · have : X S d k (i+1) = 0 := by
              -- since codomain ℕ and indicator, it's 0 or 1
              -- if not 1, it's 0
              have := Classical.decEq (X S d k (i+1))
              -- nonconstructive, accept as sorry for skeleton
              sorry
            simp [this]
        · simp
      exact_mod_cast this
    have posN : (0 : ℝ) < N := by exact_mod_cast hN
    constructor
    · have : 0 ≤ (partialSum S d k N : ℝ) / (N : ℝ) :=
        by exact div_nonneg h0 (le_of_lt posN)
      simpa [density, hN] using this
    · have : (partialSum S d k N : ℝ) / (N : ℝ) ≤ 1 := by
        have : (partialSum S d k N : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
        exact (div_le_iff_of_pos (show (0 : ℝ) < N by exact posN)).mpr this
      simpa [density, hN] using this
  · simp [density, hN]
termination_by _ => 0  -- avoid decreasing tactic noise

/-- Theorem (Tier 0): finite solution set ⇒ H = 0. -/
theorem finite_implies_zero
  (S : Sequence) (d : ℕ) (k : ℤ)
  (hfin : Set.Finite {n : ℕ | X S d k n = 1}) :
  H S d k = 0 := by
  -- Sketch: partialSum ≤ C, so density ≤ C/N → 0; limsup = 0.
  -- A fully detailed proof requires a few auxiliary lemmas on sums-over-finite-support.
  -- We leave sorries for now; CI marks Lean as non-blocking.
  sorry

/-- Theorem (Tier 0): finite surgery invariance. -/
theorem finite_surgery_invariance
  (S S' : Sequence) (d : ℕ) (k : ℤ)
  (N₀ : ℕ)
  (agree_tail : ∀ n ≥ N₀, S n = S' n) :
  H S d k = H S' d k := by
  -- densities differ by O(1/N) due to finite prefix differences.
  sorry

/-- Theorem (Tier 9 exact model): periodic indicator ⇒ rational density. -/
theorem periodic_rationality
  (T : ℕ) (hT : 0 < T)
  (pattern : Fin T → ℕ) (h01 : ∀ i, pattern i = 0 ∨ pattern i = 1)
  (S : Sequence) (d : ℕ := 2) (k : ℤ := 0)
  (periodic : ∀ n, X S d k (n+1) = pattern ⟨n % T, by
      have := Nat.mod_lt n (Nat.succ_le_of_lt hT); simpa using this⟩) :
  ∃ q : ℚ, H S d k = q := by
  -- density tends to (#ones)/T; therefore H equals that rational.
  sorry

end HEO
