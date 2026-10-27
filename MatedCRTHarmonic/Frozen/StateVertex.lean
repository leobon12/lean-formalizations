import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Dart
import MatedCRTHarmonic.Frozen.Dtgt
import MatedCRTHarmonic.Frozen.State

/-!
# Frozen definition: `LFMultigraph.stateVertex`

The current vertex of a state.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The current vertex of a state. -/
def stateVertex (s : G.State) : V := Sum.elim id G.dtgt (s : V ⊕ G.Dart)

end LFMultigraph

end MatedCRTHarmonic
