import Mathlib
import MatedCRTHarmonic.Frozen.MatedCRTPath2

/-!
# Frozen definition: `MatedCRT.brownRescale`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- Brownian rescaling of the boundary-length pair: `t ↦ b^{-1/2} ω(bt)`. -/
def brownRescale (b₀ : ℝ) (ω : Path2) : Path2 :=
  ⟨fun t => (b₀ ^ (-(1 / 2 : ℝ))) • ω (b₀ * t), by fun_prop⟩

end MatedCRT

end MatedCRTHarmonic
