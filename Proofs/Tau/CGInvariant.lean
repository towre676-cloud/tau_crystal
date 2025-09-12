import Proofs.Tau.Operational

namespace Proofs.Tau
open Proofs.Tau

-- Abstract “residual polynomial” witness model. You will later instantiate this.
structure ResidualModel where
  Witness     : Type
  proj        : State -> Witness                 -- extract residual-like witness from State
  polyId      : Witness -> Witness -> Prop       -- “w1 equals p(A)·w0” (abstract)
  polyRefl    : forall w, polyId w w
  polyTrans   : forall {a b c}, polyId a b -> polyId b c -> polyId a c
  respectsCG  : forall (st : Step) (s : State), isCG st -> polyId (proj s) (proj (stepSem st s))

def allCG : Transcript -> Prop := allSteps isCG

-- Main transport: if every step is a CG-step that respects the witness,
-- then the transcript composes the residual-polynomial identity.
theorem polyId_through (M : ResidualModel) :
  forall (s0 : State) (tr : Transcript),
    allCG tr -> M.polyId (M.proj s0) (M.proj (run s0 tr)) := by
  intro s0 tr h
  induction tr generalizing s0 with
  | nil => simpa [run] using M.polyRefl (M.proj s0)
  | cons st ts ih =>
      rcases h with ⟨hCG, hTail⟩
      have stepWitness : M.polyId (M.proj s0) (M.proj (stepSem st s0)) := M.respectsCG st s0 hCG
      have tailWitness : M.polyId (M.proj (stepSem st s0)) (M.proj (run (stepSem st s0) ts)) := ih (stepSem st s0) hTail
      simpa [run] using M.polyTrans stepWitness tailWitness

-- Optional: a tiny check that τ stays monotone when CG steps carry nonnegative inc.
def nonnegInc : Step -> Prop := fun st => st.inc > 0 || st.inc = 0

theorem tau_monotone_over_CG (s0 : State) (tr : Transcript) :
  allCG tr -> allSteps (respects (fun s => s.tick >= s0.tick)) tr ->
  (tau s0 tr) >= s0.tick := by
  intro _ hRes; have := transport (fun s => s.tick >= s0.tick) s0 tr hRes (Nat.le_refl _)
  simpa [tau]

end Proofs.Tau
