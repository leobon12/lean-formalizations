import Mathlib

/-!
# Frozen definition: `MatedCRT.firstHit`

Non-junk by surjectivity and transience .
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- First hitting time of `z` by a curve (a.s. the unique hitting time of a fixed point). -/
def firstHit (c : C(ℝ, ℂ)) (z : ℂ) : ℝ := sInf {t : ℝ | c t = z}

end MatedCRT

end MatedCRTHarmonic
