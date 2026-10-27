import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Dart

/-!
# Frozen definition: `LFMultigraph.dtgt`

The vertex a dart enters.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The vertex a dart enters. -/
def dtgt (d : G.Dart) : V := if d.2 then G.src d.1 else G.tgt d.1

end LFMultigraph

end MatedCRTHarmonic
