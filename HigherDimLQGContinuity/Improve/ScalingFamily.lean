import HigherDimLQGContinuity.Improve.SeedScalingAE
import HigherDimLQGContinuity.SiteEvents.Trials
import Mathlib.Order.Filter.Finite

/-!
# Simultaneous normalization at a finite family of candidate sites
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- All primary and seed normalization identities can be imposed at once
on a deterministic finite family. -/
theorem q11_scaling_family_ae {d : ℕ} (hd : 2 ≤ d)
    (K : CountData d) (hξ : 0 < K.ξ) (hη : 0 < K.η)
    (hD : IsStrongExpMetric d K.ξ (distExp d K.ξ) K.D)
    (hE : IsStrongExpMetric d K.η (distExp d K.η) K.E)
    {s₀ : ℝ} (hs₀ : 0 < s₀)
    (F : Finset (ℝ × Rd d)) (hF : ∀ p ∈ F, 0 < p.1)
    {ι : Type} (I : Finset ι) (centre : ι → Rd d)
    {L : ℝ} (hL : 0 < L) (Ntr : ℕ) :
    ∀ᵐ H ∂(pinLaw d s₀),
      ∀ p ∈ F,
        (countSiteD K p.1 p.2 H = rho K.D (recentre 1 p.1 p.2 H) ∧
         (∃ hratio : 0 < scaleS d K.η 1 p.1 p.2 H /
             scaleS d K.ξ 1 p.1 p.2 H,
           countSiteE K p.1 p.2 H =
           (rho K.E (recentre 1 p.1 p.2 H)).smul
             (scaleS d K.η 1 p.1 p.2 H / scaleS d K.ξ 1 p.1 p.2 H)
             hratio) ∧
         (countSiteD K p.1 p.2 H).IsLength ∧
         (countSiteE K p.1 p.2 H).IsLength) ∧
        ∀ e ∈ I, ∀ j ∈ Finset.range Ntr,
          siteNorm K.ξ K.D (centre e) (seedTrialRadius_pos hL j)
              (recentre 1 p.1 p.2 H) =
            rho K.D (recentre 1 (seedTrialRadius L j) (centre e)
              (recentre 1 p.1 p.2 H)) ∧
          siteNorm K.η K.E (centre e) (seedTrialRadius_pos hL j)
              (recentre 1 p.1 p.2 H) =
            rho K.E (recentre 1 (seedTrialRadius L j) (centre e)
              (recentre 1 p.1 p.2 H)) := by
  classical
  rw [Filter.eventually_all_finset]
  intro p hp
  have hprimary := q11_countSite_scaling hd K hξ hη hD hE hs₀ p.2 (hF p hp)
  have hseed : ∀ᵐ H ∂(pinLaw d s₀),
      ∀ e ∈ I, ∀ j ∈ Finset.range Ntr,
        siteNorm K.ξ K.D (centre e) (seedTrialRadius_pos hL j)
            (recentre 1 p.1 p.2 H) =
          rho K.D (recentre 1 (seedTrialRadius L j) (centre e)
            (recentre 1 p.1 p.2 H)) ∧
        siteNorm K.η K.E (centre e) (seedTrialRadius_pos hL j)
            (recentre 1 p.1 p.2 H) =
          rho K.E (recentre 1 (seedTrialRadius L j) (centre e)
            (recentre 1 p.1 p.2 H)) := by
    rw [Filter.eventually_all_finset]
    intro e he
    rw [Filter.eventually_all_finset]
    intro j hj
    exact q11_seed_scaling_ae hd hξ hη hD hE hs₀ (hF p hp)
      (seedTrialRadius_pos hL j) p.2 (centre e)
  filter_upwards [hprimary, hseed] with H h₁ h₂
  exact ⟨⟨h₁.1, ⟨div_pos (scaleS_pos d K.η 1 (hF p hp) p.2 H)
    (scaleS_pos d K.ξ 1 (hF p hp) p.2 H), h₁.2.1⟩,
    h₁.2.2.1, h₁.2.2.2⟩, h₂⟩

end HigherDimLQGContinuity
