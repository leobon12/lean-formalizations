import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Adj

/-!
# Frozen definition: `LFMultigraph.Disconnects`

`U` meets every graph path joining `S` to `T`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- `U` disconnects `S` from `T`: it meets every graph path joining them. -/
def Disconnects (U S T : Set V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ T, ∀ w : G.adj.Walk a b, ∃ y ∈ w.support, y ∈ U

end LFMultigraph

end MatedCRTHarmonic
