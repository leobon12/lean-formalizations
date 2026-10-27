import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.StateMeasurableSpace
import MatedCRTHarmonic.Frozen.WalkKernel
import MatedCRTHarmonic.Frozen.WalkKernelIsMarkov
import MatedCRTHarmonic.Frozen.ChainLaw

/-!
# Frozen definition: `LFMultigraph.walkLaw`

`Markov.chainLaw walkKernel (inl x)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The law of simple random walk from `x`, at the level of edge ends. -/
def walkLaw (x : V) : Measure (ℕ → G.State) :=
  Markov.chainLaw G.walkKernel (show G.State from Sum.inl x)

end LFMultigraph

end MatedCRTHarmonic
