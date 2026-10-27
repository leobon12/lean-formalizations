import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.StateMeasurableSpace
import MatedCRTHarmonic.Frozen.StateVertex
import MatedCRTHarmonic.Frozen.StepMeasure
import MatedCRTHarmonic.Frozen.StepMeasureIsProbability
import MatedCRTHarmonic.Frozen.WalkKernel

/-!
# Frozen definition: `LFMultigraph.instIsMarkovKernelStateWalkKernel`

`walkKernel` is a Markov kernel (Lean's automatic name of the candidate's anonymous instance).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

instance instIsMarkovKernelStateWalkKernel : IsMarkovKernel G.walkKernel :=
  ⟨fun s => by change IsProbabilityMeasure (G.stepMeasure _); infer_instance⟩

end LFMultigraph

end MatedCRTHarmonic
