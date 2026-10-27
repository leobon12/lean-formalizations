import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.StateMeasurableSpace
import MatedCRTHarmonic.Frozen.HitTime
import MatedCRTHarmonic.Frozen.WalkLaw
import MatedCRTHarmonic.Frozen.VertexPath

/-!
# Frozen definition: `LFMultigraph.Recurrent`

Hitting form: from every vertex the walk visits every vertex a.s. `rfl`-equal to P22's
`HarmonicInfinity.Recurrent`, which T0 c3 re-based onto this file ((4)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- **Recurrence** of simple random walk, hitting form (`rfl`-equal to `HarmonicInfinity.Recurrent`): from every vertex `x` the walk visits every vertex `y` almost surely (: "the simple random
walk on `G^ε` is recurrent"; on a connected graph this is equivalent to a.s. return). -/
def Recurrent : Prop :=
  ∀ x y : V, G.walkLaw x {ω | Markov.hitTime ({y} : Set V) (G.vertexPath ω) ≠ ⊤} = 1

end LFMultigraph

end MatedCRTHarmonic
