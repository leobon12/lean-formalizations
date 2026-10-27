import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Dart
import MatedCRTHarmonic.Frozen.Dsrc

/-!
# Frozen definition: `LFMultigraph.outDarts`

The edge ends at `x`, a finite set by local finiteness.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The edge ends at `x`: the darts leaving `x` (a finite set by local finiteness). -/
def outDarts (x : V) : Finset G.Dart := by
  classical
  exact ((G.finite_inc x).toFinset ×ˢ (Finset.univ : Finset Bool)).filter fun d => G.dsrc d = x

end LFMultigraph

end MatedCRTHarmonic
