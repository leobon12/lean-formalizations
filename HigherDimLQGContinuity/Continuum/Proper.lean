import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Fatou.Basic
import HigherDimLQGMetric.Sec10.Lemma101
import HigherDimLQGMetric.Proper.Proper
import HigherDimLQGMetric.Sec4.Lemma41Uniform

/-!
# Properness and geodesics of the strong metric

The fixed parameter result is already proved in `HigherDimLQGMetric`. This file
specializes it to the uniform parameter window used in the continuum packet.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

/-- Every strong metric in the uniform subcritical window is almost surely proper. -/
theorem continuum_proper {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    {b μ ξ : ℝ} (hξ : UHyp d κ b μ ξ)
    {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) :
    ∀ᵐ g ∂(normLGFLaw d), ProperSpace (D g).Space := by
  haveI := l9b_normLGFLaw_prob (show 2 ≤ d by omega)
  have hsub := fatou_subcritical hξ
  simpa only [id_eq] using lemma27_proper hd hsub.1 hsub.2
    (lemma101 (show 2 ≤ d by omega) hsub.1 hD)
    (normLGFLaw d) id (l9b_normLGFLaw_normalized
      (show 2 ≤ d by omega)).1

/-- Every strong metric in the uniform subcritical window is almost surely geodesic. -/
theorem continuum_geodesic {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    {b μ ξ : ℝ} (hξ : UHyp d κ b μ ξ)
    {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) :
    ∀ᵐ g ∂(normLGFLaw d), ∀ x y : Rd d,
      ∃ (γ : ℝ → Rd d) (T : ℝ),
        γ 0 = x ∧ γ T = y ∧ IsGeodesicCurve ((D g).pt ∘ γ) 0 T := by
  haveI := l9b_normLGFLaw_prob (show 2 ≤ d by omega)
  have hsub := fatou_subcritical hξ
  simpa only [id_eq] using lemma27_geodesic hd hsub.1 hsub.2
    (lemma101 (show 2 ≤ d by omega) hsub.1 hD)
    (normLGFLaw d) id (l9b_normLGFLaw_normalized
      (show 2 ≤ d by omega)).1

end HigherDimLQGContinuity
