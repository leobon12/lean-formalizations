import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Dart
import MatedCRTHarmonic.Frozen.Dtgt
import MatedCRTHarmonic.Frozen.OutDarts
import MatedCRTHarmonic.Frozen.Deg
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.StateMeasurableSpace
import MatedCRTHarmonic.Frozen.WalkLaw
import MatedCRTHarmonic.Frozen.VertexPath
import MatedCRTHarmonic.Frozen.HitTime
import MatedCRTHarmonic.Frozen.Recurrent
import MatedCRTHarmonic.Frozen.VerticesMeeting
import MatedCRTHarmonic.Frozen.MatedCRTPath2
import MatedCRTHarmonic.Frozen.MatedCRTEdge
import MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import MatedCRTHarmonic.Frozen.MatedCRTGraph
import MatedCRTHarmonic.Frozen.MatedCRTField
import MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-!
# Statement definition: `LFMultigraph.energyOn`

One of the seven definitions of the statement surface of the formalization of Gwynne–Miller–Sheffield,
*Harmonic functions on mated-CRT maps* (arXiv:1807.07511), here
called [18]. The definition is the frozen statement text, with the library namespace renamed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- **[18] Definition 1.1 on the subgraph induced by `S`**:
`Energy(g; G(S)) = ∑_{{x,y} ∈ E(G(S))} (g(x) − g(y))²`, the sum over the edges of `G` with both ends in `S` (the edges
of the induced subgraph `G(S)` of [18] (1.5)), parallel edges counted with multiplicity; a loop contributes `0`.
`ℝ≥0∞`-valued: a sum of nonnegative terms, finite for finite `S`. -/
def energyOn (S : Set V) (g : V → ℝ) : ℝ≥0∞ :=
  ∑' e : {e : E // G.src e ∈ S ∧ G.tgt e ∈ S}, ENNReal.ofReal ((g (G.src e.1) - g (G.tgt e.1)) ^ 2)

end LFMultigraph

end MatedCRTHarmonic
