import Mathlib
import MatedCRTHarmonic.Frozen.HistKernel
import MatedCRTHarmonic.Frozen.HistKernelIsMarkov

/-!
# Frozen definition: `Markov.chainLaw`

Law on `ℕ → S` of the chain with kernel `κ` from `z` (`Kernel.trajMeasure`); copy in MC.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace Markov

variable {S : Type*} [MeasurableSpace S]

/-- The law on `ℕ → S` of the chain with kernel `κ` started at `z`. -/
def chainLaw (κ : Kernel S S) [IsMarkovKernel κ] (z : S) : Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ => S) (Measure.dirac z) (histKernel κ)

end Markov

end MatedCRTHarmonic
