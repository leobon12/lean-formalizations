import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Dart

/-!
# Frozen definition: `LFMultigraph.dsrc`

The vertex a dart leaves.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The vertex a dart leaves. -/
def dsrc (d : G.Dart) : V := if d.2 then G.tgt d.1 else G.src d.1

end LFMultigraph

end MatedCRTHarmonic
