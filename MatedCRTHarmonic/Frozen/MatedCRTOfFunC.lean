import Mathlib
import MatedCRTHarmonic.Frozen.MatedCRTField

/-!
# Frozen definition: `MatedCRT.ofFunC`

Junk `0` when `f` is not locally integrable; not hit by the cone radial profile a.s. .
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The distribution `φ ↦ ∫ f φ` of a function (junk `0` if `f` is not locally integrable; mathlib `ofFun`). -/
def ofFunC (f : ℂ → ℝ) : Field := Distribution.ofFun ⊤ f volume ⊤

end MatedCRT

end MatedCRTHarmonic
