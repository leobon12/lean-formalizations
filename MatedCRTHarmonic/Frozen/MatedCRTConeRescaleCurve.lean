import Mathlib

/-!
# Frozen definition: `MatedCRT.coneRescaleCurve`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **`η^b`** : `η^b(t) = R_b⁻¹ η(bt)`. -/
def coneRescaleCurve (R b₀ : ℝ) (η : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => ((R⁻¹ : ℝ) : ℂ) * η (b₀ * t), by fun_prop⟩

end MatedCRT

end MatedCRTHarmonic
