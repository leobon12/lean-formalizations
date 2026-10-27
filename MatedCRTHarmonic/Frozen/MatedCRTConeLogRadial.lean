import Mathlib
import MatedCRTHarmonic.Frozen.MatedCRTLqgQ
import MatedCRTHarmonic.Frozen.MatedCRTConeRadial

/-!
# Frozen definition: `MatedCRT.coneLogRadial`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The radial path `s ↦ A_{−s} + Q s` of the cone (`= h_{e^s}(0) + Q s`). -/
def coneLogRadial (γ α : ℝ) (b b' : ℝ≥0 → ℝ) (s : ℝ) : ℝ := coneRadial γ α b b' (-s) + lqgQ γ * s

end MatedCRT

end MatedCRTHarmonic
