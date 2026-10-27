import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.StateVertex

/-!
# Frozen definition: `LFMultigraph.vertexPath`

The vertex path `X_n` of an edge-end path.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The vertex path `X_n` of an edge-end path. -/
def vertexPath (ω : ℕ → G.State) : ℕ → V := fun n => G.stateVertex (ω n)

end LFMultigraph

end MatedCRTHarmonic
