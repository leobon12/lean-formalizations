import Mathlib
import MatedCRTHarmonic.Frozen.MatedCRTIntervalInf

/-!
# Frozen definition: `MatedCRT.SideCond`

Condition (1.1) literally (`max` is `∨`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- Condition (1.1) of Definition 1.12 for one coordinate `X ∈ {L, R}` and the vertices `εx < εy`
(vertex `x : ℤ` stands for the point `εx ∈ εℤ`):
`inf_{[εx−ε, εx]} X ∨ inf_{[εy−ε, εy]} X ≤ inf_{[εx, εy−ε]} X`. -/
def SideCond (ε : ℝ) (X : ℝ → ℝ) (x y : ℤ) : Prop :=
  max (intervalInf X (ε * ((x : ℝ) - 1)) (ε * x)) (intervalInf X (ε * ((y : ℝ) - 1)) (ε * y)) ≤
    intervalInf X (ε * x) (ε * ((y : ℝ) - 1))

end MatedCRT

end MatedCRTHarmonic
