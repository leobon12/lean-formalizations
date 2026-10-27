import Mathlib

/-!
# Frozen definition: `MatedCRT.dyadicScale`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- Dyadic scale `2^{-k}`. -/
def dyadicScale (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℤ))

end MatedCRT

end MatedCRTHarmonic
