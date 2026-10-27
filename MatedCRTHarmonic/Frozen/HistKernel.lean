import Mathlib

/-!
# Frozen definition: `Markov.histKernel`

History kernel of a time-homogeneous chain. The landed module `MatedCRTHarmonic/Markov/Chain.lean` (MC)
has an `rfl`-equal copy under the same name; re-basing MC onto this file is Q7.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace Markov

variable {S : Type*} [MeasurableSpace S]

/-- The history kernel of a time-homogeneous chain: the next state is drawn from `κ` at the last state. -/
def histKernel (κ : Kernel S S) (n : ℕ) : Kernel (Π _ : Finset.Iic n, S) S :=
  κ.comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

end Markov

end MatedCRTHarmonic
