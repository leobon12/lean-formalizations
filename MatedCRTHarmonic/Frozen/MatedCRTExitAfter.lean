import Mathlib
import MatedCRTHarmonic.Frozen.MatedCRTFirstHit

/-!
# Frozen definition: `MatedCRT.exitAfter`

Non-junk by surjectivity and transience .
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- `S_z`: the first time `c` exits `U` after hitting `z`. -/
def exitAfter (c : C(ℝ, ℂ)) (U : Set ℂ) (z : ℂ) : ℝ := sInf {t : ℝ | firstHit c z ≤ t ∧ c t ∉ U}

end MatedCRT

end MatedCRTHarmonic
