import HigherDimLQGContinuity.Caps.Grid
import HigherDimLQGContinuity.Norm.PinGauss
import HigherDimLQGMetric.Sharp.W2Gaussian

/-!
# A finite-family sphere-average cap (packet P4)

This is the Gaussian probability step of Lemma 2.2. The grid count and the
uniform variance estimate are separate deterministic steps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory ProbabilityTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Union bound for finitely many pinned sphere averages. -/
theorem p4_cap_finite {d : ℕ} (hd : 2 ≤ d) {s s₀ V T t : ℝ}
    (hs₀ : 0 < s₀) (F : Finset (ℝ × Rd d))
    (hF : ∀ p ∈ F, 0 < s * p.1)
    (hV : ∀ p ∈ F,
      Var[fun g : DistRd d => sphereAvg g (s * p.1) p.2; pinLaw d s₀] ≤ V)
    (ht : 0 ≤ t) :
    pinLaw d s₀ {g | ∃ p ∈ F, T < |sphereAvg g (s * p.1) p.2|} ≤
      ENNReal.ofReal ((F.card : ℝ) * (2 * Real.exp (-t * T + t ^ 2 * V / 2))) := by
  have := isProbabilityMeasure_pinLaw hd s₀
  apply w2_gaussian_finset_union F
    (fun p g => sphereAvg g (s * p.1) p.2)
  · intro p hp
    exact (hasGaussianLaw_sphereAvg_pinLaw hd hs₀ (hF p hp) p.2).1
  · intro p hp
    exact (hasGaussianLaw_sphereAvg_pinLaw hd hs₀ (hF p hp) p.2).2
  · exact hV
  · exact ht

end HigherDimLQGContinuity
