import Mathlib

/-!
# Frozen definition: `MatedCRT.lrCov`

Unit-time covariance matrix `[[1, c], [c, 1]]`, `c = −cos(πγ²/4)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The covariance matrix per unit time of Definition 1.12 : `Var(L_1) = Var(R_1) = 1`,
`Cov(L_1, R_1) = −cos(πγ²/4)`. -/
def lrCov (γ : ℝ) (i j : Fin 2) : ℝ := if i = j then 1 else -Real.cos (Real.pi * γ ^ 2 / 4)

end MatedCRT

end MatedCRTHarmonic
