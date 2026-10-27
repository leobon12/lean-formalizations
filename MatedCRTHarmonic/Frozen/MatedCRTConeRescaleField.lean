import Mathlib
import LQGMetric.Statement.GFF
import MatedCRTHarmonic.Frozen.MatedCRTField
import MatedCRTHarmonic.Frozen.MatedCRTLqgQ

/-!
# Frozen definition: `MatedCRT.coneRescaleField`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **`h_b`** : `h_b = h(R_b ·) + Q log R_b − γ⁻¹ log b`. -/
def coneRescaleField (γ R b₀ : ℝ) (h : Field) : Field :=
  LQGMetric.addConst (LQGMetric.affineComp R 0 h) (lqgQ γ * Real.log R - γ⁻¹ * Real.log b₀)

end MatedCRT

end MatedCRTHarmonic
