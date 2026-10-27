import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Dart
import MatedCRTHarmonic.Frozen.OutDarts
import MatedCRTHarmonic.Frozen.Deg
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.StateMeasurableSpace

/-!
# Frozen definition: `LFMultigraph.stepMeasure`

Literal, with no fallback branch: `deg x ≠ 0` by `exists_inc`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- One step of simple random walk from `x`: a uniformly chosen edge end at `x`. -/
def stepMeasure (x : V) : Measure G.State :=
  (G.deg x : ℝ≥0∞)⁻¹ • ∑ d ∈ G.outDarts x, Measure.dirac (show G.State from Sum.inr d)

end LFMultigraph

end MatedCRTHarmonic
