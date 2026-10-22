import HigherDimLQGContinuity.ForcingCount.SiteNorm
import HigherDimLQGContinuity.LabelEvents.SiteNormal

/-!
# Identifying the forcing-count site metrics with the site-normal API
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem q11_countSiteD_eq_siteNorm {d : ℕ} (K : CountData d)
    {s : ℝ} (hs : 0 < s) (z : Rd d) (H : DistRd d) :
    countSiteD K s z H = siteNorm K.ξ K.D z hs H := by
  have hS : 0 < countUnit K s z H := scaleS_pos d K.ξ 1 hs z H
  rw [countSiteD, q9SiteNorm_eq hs hS]
  rfl

theorem q11_countSiteE_eq_siteNorm {d : ℕ} (K : CountData d)
    {s : ℝ} (hs : 0 < s) (z : Rd d) (H : DistRd d) :
    countSiteE K s z H = siteNorm K.ξ K.E z hs H := by
  have hS : 0 < countUnit K s z H := scaleS_pos d K.ξ 1 hs z H
  rw [countSiteE, q9SiteNorm_eq hs hS]
  rfl

/-- The Q5 normalization theorem applies verbatim to the Q9 count metrics. -/
theorem q11_countSite_scaling {d : ℕ} (hd : 2 ≤ d)
    (K : CountData d) (hξ : 0 < K.ξ) (hη : 0 < K.η)
    (hD : IsStrongExpMetric d K.ξ (distExp d K.ξ) K.D)
    (hE : IsStrongExpMetric d K.η (distExp d K.η) K.E)
    {s₀ s : ℝ} (hs₀ : 0 < s₀) (z : Rd d) (hs : 0 < s) :
    ∀ᵐ H ∂(pinLaw d s₀),
      countSiteD K s z H = rho K.D (recentre 1 s z H) ∧
      countSiteE K s z H =
        (rho K.E (recentre 1 s z H)).smul
          (scaleS d K.η 1 s z H / scaleS d K.ξ 1 s z H)
          (div_pos (scaleS_pos d K.η 1 hs z H) (scaleS_pos d K.ξ 1 hs z H)) ∧
      (countSiteD K s z H).IsLength ∧ (countSiteE K s z H).IsLength := by
  filter_upwards [siteNormal_scaling hd hξ hη hD hE hs₀ z hs] with H hH
  simpa only [← q11_countSiteD_eq_siteNorm K hs z H,
    ← q11_countSiteE_eq_siteNorm K hs z H] using hH

end HigherDimLQGContinuity
