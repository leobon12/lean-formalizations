import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Dart
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.HitTime
import MatedCRTHarmonic.Frozen.VertexPath
import MatedCRTHarmonic.Frozen.StateMeasurableSpace
import MatedCRTHarmonic.Frozen.WalkLaw
import MatedCRTHarmonic.Frozen.Adj
import MatedCRTHarmonic.Harmonic.Walk

/-!
# Harmonic measure from a point and from infinity

* `harm_isProbability_holds`: on a connected locally finite multigraph, for nonempty `A` and
  `x ∉ A`, `harm^x_A` is a probability vector carried by the edge boundary of `A` (the entry-edge argument).
  The walk from `x` hits `A` with positive probability (`hitProb_pos`); almost surely its entry
  state is a dart from outside `A` into `A` (`exists_entryEdge`), whose edge is a boundary edge.
* `harmInf_eq_of_hasHarmInf_holds`: `harmInf A` is the limit whenever one exists (the filter
  `awayFrom A` is proper on infinite graphs).
* `hasHarmInf_isProbability`: every limit `harm^∞_A` is a probability vector carried by the
  (finite) edge boundary (the harmonic-measure argument).
* `not_halfLine_hasHarmInf_zero_holds`: the non-junk check of.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace MatedCRTHarmonic.Harmonic

open LFMultigraph Markov

variable {V E : Type*} (G : LFMultigraph V E)

/-- The entry edge read off a state. -/
def stateEdge (s : G.State) : Option E := Sum.elim (fun _ => none) (fun d => some d.1) (s : V ⊕ G.Dart)

theorem stateEdge_dartState (d : G.Dart) : stateEdge G (dartState G d) = some d.1 := rfl

theorem measurableSet_hitTime_ne_top (A : Set V) :
    MeasurableSet {ω : ℕ → G.State | hitTime A (G.vertexPath ω) ≠ ⊤} :=
  (measurableSet_hitTime_eq_top (A := G.stateVertex ⁻¹' A) MeasurableSet.of_discrete).compl

/-! ### The half-line -/

end MatedCRTHarmonic.Harmonic
