import Mathlib

/-!
# Frozen definition: `MatedCRT.twoSidedMin`

Covariance kernel `|s| ∧ |t|` on the same side of `0`, `0` otherwise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The covariance kernel of two-sided standard Brownian motion: `|s| ∧ |t|` if `s` and `t` lie on the same side of
`0`, and `0` otherwise. -/
def twoSidedMin (s t : ℝ) : ℝ := min (max s 0) (max t 0) + min (max (-s) 0) (max (-t) 0)

end MatedCRT

end MatedCRTHarmonic
