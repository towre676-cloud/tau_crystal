import Mathlib

namespace Tau.Distance

/-- Fisher geodesic length √((n c)/(2 b)) * |log(μ/μ₀)|. -/
def fisherLen (n c b mu mu0 : ℝ) : ℝ :=
  Real.sqrt ((n * c) / (2 * b)) * |Real.log (mu / mu0)|

end Tau.Distance
