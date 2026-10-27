import Mathlib
import MatedCRTHarmonic.Frozen.HistKernel

/-!
# Frozen definition: `Markov.histKernel_isMarkovKernel`

Copy in MC.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace Markov

variable {S : Type*} [MeasurableSpace S]

instance histKernel_isMarkovKernel (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (histKernel κ n) := by
  unfold histKernel; infer_instance

end Markov

end MatedCRTHarmonic
