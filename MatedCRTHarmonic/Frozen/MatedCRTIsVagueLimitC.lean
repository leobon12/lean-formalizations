import Mathlib

/-!
# Frozen definition: `MatedCRT.IsVagueLimitC`

The coupling statement quantifies over every dyadic vague limit of the area approximations.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- Vague convergence on `ℂ` (locally finite limit; integrals of compactly supported continuous functions). -/
def IsVagueLimitC (μs : ℕ → Measure ℂ) (μ : Measure ℂ) : Prop :=
  (∀ K : Set ℂ, IsCompact K → μ K < ⊤) ∧
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 (∫ z, f z ∂μ))

end MatedCRT

end MatedCRTHarmonic
