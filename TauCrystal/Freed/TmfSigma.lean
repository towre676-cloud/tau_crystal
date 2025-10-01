/-! Capsule shell: σ‑orientation hook; to be backed by emitted q‑series receipts. -/
namespace TauCrystal.Freed
structure QSeries where coeffs : Nat → Int
def sigmaOrient (q : QSeries) : Bool := True
end TauCrystal.Freed
