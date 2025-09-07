import Lean
open Lean Json
structure LaurentResidue where real : Float; imag : Float; abs : Float deriving FromJson
structure LaurentSummary where
  kappa_A : Float; nu : Int; residue_a_minus_1 : LaurentResidue;
  norm_R : Float; norm_D : Float; E_rstar : Float; r_star : Float; r_min : Float; r_max : Float; conf : Float
deriving FromJson
structure LaurentSignature where summary : LaurentSummary deriving FromJson
def validateLaurent (j : Json) : Except String LaurentSignature := do
  let sig ← fromJson? j |>.toExcept "parse laurent_signature failed"
  if sig.summary.nu < 0 then throw "nu must be ≥ 0"
  if sig.summary.residue_a_minus_1.abs < 0.0 then throw "|a_{-1}| < 0?"
  if sig.summary.kappa_A < 0.0 then throw "kappa_A < 0"
  pure sig
