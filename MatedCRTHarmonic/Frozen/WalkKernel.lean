import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.StateMeasurableSpace
import MatedCRTHarmonic.Frozen.StateVertex
import MatedCRTHarmonic.Frozen.StepMeasure

/-!
# Frozen definition: `LFMultigraph.walkKernel`

The time-homogeneous transition kernel of the edge-end walk: one step from the current vertex.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The transition kernel of the edge-end walk: step from the current vertex. -/
def walkKernel : Kernel G.State G.State where
  toFun s := G.stepMeasure (G.stateVertex s)
  measurable' := measurable_from_top

end LFMultigraph

end MatedCRTHarmonic
