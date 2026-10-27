import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Adj

/-!
# Frozen definition: `LFMultigraph.IsConnectedSet`

The induced subgraph on `A` is connected.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- `A` is connected: its induced subgraph is connected. -/
def IsConnectedSet (A : Set V) : Prop := (G.adj.induce A).Connected

end LFMultigraph

end MatedCRTHarmonic
