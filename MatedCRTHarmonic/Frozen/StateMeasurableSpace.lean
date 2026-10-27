import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.State

/-!
# Frozen definition: `LFMultigraph.instMeasurableSpaceState`

The discrete σ-algebra `⊤` on `State`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

instance instMeasurableSpaceState : MeasurableSpace G.State := ⊤

end LFMultigraph

end MatedCRTHarmonic
