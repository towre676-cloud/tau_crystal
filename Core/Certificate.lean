import Std
import Core.Tau
import Core.Sheaf
import Core.Residue

open Tau TinySheaf Residue

/-- Bronze-tier toy certificate. -/
structure BronzeCertificate where
  tauCover : TauCover
  locals   : List (Section Float)
  glue_ok  : TinySheaf.Glues locals
  toy_cpx  : Residue.Cpx Float (Float Ãƒâ€” Float) PUnit
  d2_zero  : Ã¢Ë†â‚¬ x, toy_cpx.d1 (toy_cpx.d0 x) = ()

/-- Minimal Bronze: constant section over two samples. -/
def trivialBronze : BronzeCertificate :=
  let s1 : Tau.Sample := Ã¢Å¸Â¨0.0, 0.0, 1.0Ã¢Å¸Â©
  let s2 : Tau.Sample := Ã¢Å¸Â¨0.1, 1.0, 1.0Ã¢Å¸Â©
  let w  : List Tau.Sample := [s1, s2]
  let cover : TauCover := { windows := [w] }
  let ÃÆ’ : Section Float :=
    { window := w, eval := fun _ => 1.0, dom_ok := by intro _ _; trivial }
  let locals := [ÃÆ’]
  { tauCover := cover
  , locals   := locals
  , glue_ok  := TinySheaf.glues_singleton ÃÆ’
  , toy_cpx  := Residue.toy Float
  , d2_zero  := by intro _; rfl }

/-- Quick demo: ÃŽÂµ/ÃŽÂ´ gluing for two sections via Ãâ€žÃ¢â‚¬â€˜nearby pairs. -/
def demoTwoSectionsOK : Bool :=
  let s1 : Tau.Sample := Ã¢Å¸Â¨0.0, 0.0, 1.0000001Ã¢Å¸Â©
  let s2 : Tau.Sample := Ã¢Å¸Â¨0.1, 1.0, 0.9999999Ã¢Å¸Â©
  let w  : List Tau.Sample := [s1, s2]
  let ÃÆ’ : Section Float := { window := w, eval := (Ã‚Â·.val), dom_ok := by intro _ _; trivial }
  let Ãâ€ž : Section Float := { window := w, eval := (Ã‚Â·.val), dom_ok := by intro _ _; trivial }
  TinySheaf.gluesNumericPairs [ÃÆ’, Ãâ€ž] (ÃŽÂµ := 1e-6) (ÃŽÂ´ := 1e-6)

/-- Silver-tier numeric certificate with ÃŽÂµ/ÃŽÂ´ checks + Ãâ€žÃ¢â‚¬â€˜monotone booleans. -/
structure SilverCertificate where
  tauCover      : TauCover
  locals        : List (Section Float)
  epsilon       : Float
  delta         : Float
  glue_pairs_ok : Bool
  monotone_ok   : Bool
  toy_cpx       : Residue.Cpx Float (Float Ãƒâ€” Float) PUnit
  d2_zero       : Ã¢Ë†â‚¬ x, toy_cpx.d1 (toy_cpx.d0 x) = ()

def mkSilverDemo : SilverCertificate :=
  let s1 : Tau.Sample := Ã¢Å¸Â¨0.0, 0.0, 1.000001Ã¢Å¸Â©
  let s2 : Tau.Sample := Ã¢Å¸Â¨0.1, 1.0, 0.999999Ã¢Å¸Â©
  let w  : List Tau.Sample := [s1, s2]
  let cover : TauCover := { windows := [w] }
  let ÃÆ’ : Section Float := { window := w, eval := (Ã‚Â·.val), dom_ok := by intro _ _; trivial }
  let Ãâ€ž : Section Float := { window := w, eval := fun s => s.val + 1e-7, dom_ok := by intro _ _; trivial }
  let locals := [ÃÆ’, Ãâ€ž]
  let ÃŽÂµ := 1e-6
  let ÃŽÂ´ := 1e-6
  { tauCover      := cover
  , locals        := locals
  , epsilon       := ÃŽÂµ
  , delta         := ÃŽÂ´
  , glue_pairs_ok := TinySheaf.gluesNumericPairs locals ÃŽÂµ ÃŽÂ´
  , monotone_ok   := Tau.coverTauMonotone cover
  , toy_cpx       := Residue.toy Float
  , d2_zero       := by intro _; rfl }

