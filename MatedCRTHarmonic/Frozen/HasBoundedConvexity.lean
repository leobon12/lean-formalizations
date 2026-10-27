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
# Statement definition: `HasBoundedConvexity`

One of the seven definitions of the statement surface of the formalization of Gwynne–Miller–Sheffield,
*Harmonic functions on mated-CRT maps* (arXiv:1807.07511), here
called [18]. The definition is the frozen statement text, with the library namespace renamed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

/-- **`C`-bounded convexity** ([18] Theorem 3.2, condition 2; the "bounded convexity" of Theorem 1.3 is
`∃ C > 0` of it): any two points `z, w ∈ D` are joined by a path in `D` of Euclidean length at most `C|z − w|` (a
continuous `c : [0, 1] → D` from `z` to `w`; its length is its total variation `eVariationOn`). -/
def HasBoundedConvexity (C : ℝ) (D : Set ℂ) : Prop :=
  ∀ z ∈ D, ∀ w ∈ D, ∃ c : ℝ → ℂ, ContinuousOn c (Icc 0 1) ∧ c 0 = z ∧ c 1 = w ∧
    MapsTo c (Icc 0 1) D ∧ eVariationOn c (Icc 0 1) ≤ ENNReal.ofReal (C * dist z w)

end MatedCRTHarmonic
