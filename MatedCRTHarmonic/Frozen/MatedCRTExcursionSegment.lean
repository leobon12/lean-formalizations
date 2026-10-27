import Mathlib
import MatedCRTHarmonic.Frozen.MatedCRTEntryBefore
import MatedCRTHarmonic.Frozen.MatedCRTExitAfter

/-!
# Frozen definition: `MatedCRT.excursionSegment`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The excursion segment `c(T_z + ·)|_{[0, S_z − T_z]}`, extended by constants ([18], (2.7)). -/
def excursionSegment (c : C(ℝ, ℂ)) (U : Set ℂ) (z : ℂ) : ℝ → ℂ :=
  fun u => c (entryBefore c U z + max 0 (min u (exitAfter c U z - entryBefore c U z)))

end MatedCRT

end MatedCRTHarmonic
