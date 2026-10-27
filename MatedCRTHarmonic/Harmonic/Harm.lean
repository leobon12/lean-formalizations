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
# Entry states and hitting events of the walk

* `stateEdge`: the edge of a dart state; `measurableSet_hitTime_ne_top`: the event that the walk
  hits a set is measurable.
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
