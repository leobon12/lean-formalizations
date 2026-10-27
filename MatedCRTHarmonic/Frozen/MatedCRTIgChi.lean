import Mathlib

/-!
# Frozen definition: `MatedCRT.igChi`

`χ = 2/√κ − √κ/2` for `κ = γ²`; positive for `γ ∈ (0, 2)` (S1Y probe N5).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- Imaginary-geometry constant `χ = 2/√κ − √κ/2` for the flow-line parameter `κ = γ² = 16/κ'` (IG1, (4.1);
[18]; [20]). -/
def igChi (γ : ℝ) : ℝ := 2 / γ - γ / 2

end MatedCRT

end MatedCRTHarmonic
