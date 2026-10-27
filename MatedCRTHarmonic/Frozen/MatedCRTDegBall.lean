import Mathlib

/-!
# Frozen definition: `MatedCRT.degBall`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- `B′ = B̄_{4 diam c([−1,1])}(0)` ([20] (4.19), [20]). -/
def degBall (c : C(ℝ, ℂ)) : Set ℂ := closedBall 0 (4 * diam (c '' Icc (-1) 1))

end MatedCRT

end MatedCRTHarmonic
