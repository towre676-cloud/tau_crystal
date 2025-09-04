namespace TauCrystal.Edition

inductive Kind | Community | Enterprise
deriving Repr, DecidableEq

@[inline] def current : Kind := Kind.Community

@[inline] def name : String :=
  match current with
  | Kind.Community  => "τ‑Crystal Community"
  | Kind.Enterprise => "τ‑Crystal Enterprise"

@[inline] def goldFeaturesEnabled : Bool :=
  match current with
  | Kind.Community  => false
  | Kind.Enterprise => true

end TauCrystal.Edition
