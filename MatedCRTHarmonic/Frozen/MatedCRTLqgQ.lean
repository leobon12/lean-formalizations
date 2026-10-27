import Mathlib

/-!
# Frozen definition: `MatedCRT.lqgQ`

`Q = 2/γ + γ/2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- `Q = 2/γ + γ/2`. -/
def lqgQ (γ : ℝ) : ℝ := 2 / γ + γ / 2

end MatedCRT

end MatedCRTHarmonic
