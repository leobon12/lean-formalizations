import HigherDimLQGContinuity.Improve.CountNorm

/-!
# Exact seed normalization after a primary-site recentering
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- At any fixed primary site and seed pair, both own-unit seed metrics
agree almost surely with their twice-recentered strong metrics. -/
theorem q11_seed_scaling_ae {d : ℕ} (hd : 2 ≤ d)
    {ξ η : ℝ} (hξ : 0 < ξ) (hη : 0 < η)
    {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hE : IsStrongExpMetric d η (distExp d η) E)
    {s₀ s r : ℝ} (hs₀ : 0 < s₀) (hs : 0 < s) (hr : 0 < r)
    (z c : Rd d) :
    ∀ᵐ H ∂(pinLaw d s₀),
      siteNorm ξ D c hr (recentre 1 s z H) =
        rho D (recentre 1 r c (recentre 1 s z H)) ∧
      siteNorm η E c hr (recentre 1 s z H) =
        rho E (recentre 1 r c (recentre 1 s z H)) := by
  have hDae : ∀ᵐ g ∂(pinLaw d 1),
      siteNorm ξ D c hr g = rho D (recentre 1 r c g) :=
    (siteNormal_scaling hd hξ hξ hD hD one_pos c hr).mono fun _ h => h.1
  have hEae : ∀ᵐ g ∂(pinLaw d 1),
      siteNorm η E c hr g = rho E (recentre 1 r c g) :=
    (siteNormal_scaling hd hη hη hE hE one_pos c hr).mono fun _ h => h.1
  exact ae_recentre_of_ae hd one_pos hs₀ hs z (hDae.and hEae)

end HigherDimLQGContinuity
