import Mathlib
import LQGMetric.Statement.GFF
import MatedCRTHarmonic.Frozen.MatedCRTField
import MatedCRTHarmonic.Frozen.MatedCRTDyadicScale

/-!
# Frozen definition: `MatedCRT.lqgAreaApprox`

The circle averages are LQGMetric `circleAvg` (a `limUnder`), correct for a.e. `z` a.s. .
With R1 the bundle quantifies over every dyadic vague limit; its a.s. existence for both cone fields is the closure
anchor R4 NJ1 (proved, `MesoModel/FrozenIdentities.lean`), not an input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The area approximation `2^{-kγ²/2} e^{γ h_{2^{-k}}(z)} dz`. -/
def lqgAreaApprox (γ : ℝ) (h : Field) (k : ℕ) : Measure ℂ :=
  volume.withDensity fun z : ℂ =>
    ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * LQGMetric.circleAvg h (dyadicScale k) z))

end MatedCRT

end MatedCRTHarmonic
