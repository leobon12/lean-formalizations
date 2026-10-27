import Mathlib
import LQGMetric.Statement.GFF
import MatedCRTHarmonic.Frozen.MatedCRTField

/-!
# Frozen definition: `MatedCRT.radialAvg`

The radial circle-average process of the mated-CRT cone field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The radial profile `z ↦ h_{|z|}(0)` (circle averages about `0`, LQGMetric `circleAvg`). -/
def radialAvg (h : Field) : ℂ → ℝ := fun z => LQGMetric.circleAvg h ‖z‖ 0

end MatedCRT

end MatedCRTHarmonic
