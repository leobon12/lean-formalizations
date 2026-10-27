import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Dart
import MatedCRTHarmonic.Frozen.OutDarts

/-!
# Frozen definition: `LFMultigraph.deg`

The number of edge ends at `x`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The degree: number of edge ends at `x`, loops counted twice. -/
def deg (x : V) : ℕ := (G.outDarts x).card

end LFMultigraph

end MatedCRTHarmonic
