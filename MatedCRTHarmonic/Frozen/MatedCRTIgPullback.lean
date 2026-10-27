import Mathlib
import MatedCRTHarmonic.Frozen.MatedCRTIgChi

/-!
# Frozen definition: `MatedCRT.igPullback`

`(h ∘ ψ)_ρ(w) = h_{sρ}(ψ w)`, minus `χφ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The circle-average process of `h ∘ ψ − χφ` from that of `h`, `ψ w = z₀ + s e^{iφ} w` (IG1, (1.4)). -/
def igPullback (γ : ℝ) (z₀ : ℂ) (s φ : ℝ) (H : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun ρ w => H (s * ρ) (z₀ + (s : ℂ) * Complex.exp (φ * Complex.I) * w) - igChi γ * φ

end MatedCRT

end MatedCRTHarmonic
