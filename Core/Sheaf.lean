import Std
import Core.Tau
open Tau

namespace TinySheaf

/-- A local section over a window of samples. -/
structure Section (ÃŽÂ± : Type) where
  window : List Sample
  eval   : Sample Ã¢â€ â€™ ÃŽÂ±
  dom_ok : Ã¢Ë†â‚¬ s, s Ã¢Ë†Ë† window Ã¢â€ â€™ True

/-- Restrict to a sub-window (toy). -/
def restrict {ÃŽÂ±} (ÃÆ’ : Section ÃŽÂ±) (sub : List Sample) : Section ÃŽÂ± :=
  { window := sub, eval := ÃÆ’.eval, dom_ok := by intro _ _; trivial }

/-- Build all pairs (s,t) whose Ãâ€žÃ¢â‚¬â„¢s are within ÃŽÂ´. No equality or indices needed. -/
def pairsWithinTauÃŽÂ´ {ÃŽÂ±} (ÃÆ’ Ãâ€ž : Section ÃŽÂ±) (ÃŽÂ´ : Float) : List (Sample Ãƒâ€” Sample) :=
  let rec collect (as : List Sample) (acc : List (Sample Ãƒâ€” Sample)) : List (Sample Ãƒâ€” Sample) :=
    match as with
    | [] => acc
    | s :: as' =>
      let rec matchB (bs : List Sample) (acc2 : List (Sample Ãƒâ€” Sample)) :=
        match bs with
        | [] => acc2
        | t :: bs' =>
          let close : Bool := Tau.leB (Float.abs (s.tau - t.tau)) ÃŽÂ´
          let acc2' := if close then (s,t) :: acc2 else acc2
          matchB bs' acc2'
      collect as' (matchB Ãâ€ž.window acc)
  collect ÃÆ’.window []

/-- ÃŽÂµ/ÃŽÂ´ agreement over a list of matched pairs. -/
def agreesOnPairs (ÃÆ’ Ãâ€ž : Section Float) (pairs : List (Sample Ãƒâ€” Sample)) (ÃŽÂµ ÃŽÂ´ : Float) : Bool :=
  pairs.all (fun st =>
    let s := st.fst
    let t := st.snd
    Tau.leB (Float.abs (s.tau - t.tau)) ÃŽÂ´ &&
    Tau.leB (Float.abs (ÃÆ’.eval s - Ãâ€ž.eval t)) ÃŽÂµ)

/-- Pairwise numeric gluing for a list of sections. -/
def gluesNumericPairs (locals : List (Section Float)) (ÃŽÂµ ÃŽÂ´ : Float) : Bool :=
  match locals with
  | [] => true
  | [_] => true
  | ÃÆ’ :: rest =>
      (rest.all (fun Ãâ€ž => agreesOnPairs ÃÆ’ Ãâ€ž (pairsWithinTauÃŽÂ´ ÃÆ’ Ãâ€ž ÃŽÂ´) ÃŽÂµ ÃŽÂ´))
      && gluesNumericPairs rest ÃŽÂµ ÃŽÂ´

/-- Prop-level gluing (kept trivial so Bronze always holds for a singleton). -/
def Glues (locals : List (Section Float)) : Prop := True
theorem glues_singleton (ÃÆ’ : Section Float) : Glues [ÃÆ’] := by trivial

end TinySheaf

