import Mathlib
import MatedCRTHarmonic.Frozen.MatedCRTPath2

/-!
# Frozen definition: `MatedCRT.lrCoord`

The coordinates `L_t`, `R_t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The coordinates of a path: `lrCoord 0 t ω = L_t`, `lrCoord 1 t ω = R_t`. -/
def lrCoord (i : Fin 2) (t : ℝ) (ω : Path2) : ℝ := if i = 0 then (ω t).1 else (ω t).2

end MatedCRT

end MatedCRTHarmonic
