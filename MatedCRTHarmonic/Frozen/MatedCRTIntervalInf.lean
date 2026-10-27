import Mathlib

/-!
# Frozen definition: `MatedCRT.intervalInf`

Junk: `sInf ∅ = 0` only for an empty interval, which needs `ε < 0`; every theorem has `0 < ε`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- `inf_{[a, b]} X` (attained when `X` is continuous and `a ≤ b`). -/
def intervalInf (X : ℝ → ℝ) (a b : ℝ) : ℝ := sInf (X '' Icc a b)

end MatedCRT

end MatedCRTHarmonic
