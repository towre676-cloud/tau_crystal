namespace Proofs.Tau

-- A tiny, instrument-level semantics with a τ-like tick.
structure Step where
  tag   : String     -- e.g., "cg", "work", ...
  inc   : Nat        -- τ-increment carried by the instrument
  data  : List Int := []
deriving Repr, DecidableEq

abbrev Transcript := List Step

structure State where
  tick : Nat := 0
deriving Repr, DecidableEq

def stepSem (st : Step) (s : State) : State := { tick := s.tick + st.inc }

def run : State -> Transcript -> State
| s, []        => s
| s, st :: ts  => run (stepSem st s) ts

def tau (s0 : State) (tr : Transcript) : Nat := (run s0 tr).tick

def sumInc : Transcript -> Nat
| []       => 0
| st :: ts => st.inc + sumInc ts

lemma sumInc_append : forall (a b : Transcript), sumInc (a ++ b) = sumInc a + sumInc b := by
  intro a b; induction a with
  | nil => simp [sumInc]
  | cons st as ih => simp [sumInc, List.cons_append, ih, Nat.add_assoc]

theorem tau_eq (s0 : State) (tr : Transcript) : tau s0 tr = s0.tick + sumInc tr := by
  induction tr generalizing s0 with
  | nil => simp [tau, run, sumInc]
  | cons st ts ih =>
      simp [tau, run, sumInc, ih, Nat.add_assoc]

def isCG (st : Step) : Prop := st.tag = "cg"

def respects (P : State -> Prop) (st : Step) : Prop :=
  forall s, P s -> P (stepSem st s)

def allSteps (Q : Step -> Prop) : Transcript -> Prop
| []        => True
| st :: ts  => Q st ∧ allSteps Q ts

theorem transport (P : State -> Prop) : forall (s0 : State) (tr : Transcript),
  (allSteps (respects P) tr) -> P s0 -> P (run s0 tr) := by
  intro s0 tr hAll hP; induction tr generalizing s0 with
  | nil => simpa [run]
  | cons st ts ih =>
      rcases hAll with ⟨hStep, hTail⟩
      have hP1 : P (stepSem st s0) := hStep s0 hP
      simpa [run] using ih (stepSem st s0) hTail hP1

end Proofs.Tau
