import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteInternalLFPP
import LQGMetric.Papers.GM.S3.GoodAnnulusMeas

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem setDist_spheres_le_mul_of_internal_le
    (D E : ContMetric) (hD : D.IsLength) (hE : E.IsLength)
    (V : Set ℂ) (z : ℂ) (ρ₁ ρ₂ : ℝ) (hρ : ρ₁ < ρ₂)
    (hsub : ∀ w : ℂ, ρ₁ ≤ ‖w - z‖ → ‖w - z‖ ≤ ρ₂ → w ∈ V)
    (k : ℝ≥0∞) (hk0 : k ≠ 0) (hkTop : k ≠ ∞)
    (hcmp : ∀ x ∈ Metric.sphere z ρ₁, ∀ y ∈ Metric.sphere z ρ₂,
      E.internal V x y ≤ k * D.internal V x y) :
    setDist E (Metric.sphere z ρ₁) (Metric.sphere z ρ₂) ≤
      k * setDist D (Metric.sphere z ρ₁) (Metric.sphere z ρ₂) := by
  rw [LQGMetric.GM.setDist_spheres_eq_internal E hE hρ hsub,
    LQGMetric.GM.setDist_spheres_eq_internal D hD hρ hsub]
  calc
    (⨅ x ∈ Metric.sphere z ρ₁, ⨅ y ∈ Metric.sphere z ρ₂, E.internal V x y)
      ≤ (⨅ x ∈ Metric.sphere z ρ₁, ⨅ y ∈ Metric.sphere z ρ₂,
          k * D.internal V x y) :=
        iInf₂_mono fun x hx => iInf₂_mono fun y hy => hcmp x hx y hy
    _ = k * (⨅ x ∈ Metric.sphere z ρ₁, ⨅ y ∈ Metric.sphere z ρ₂,
          D.internal V x y) := by
        simp only [ENNReal.mul_iInf_of_ne hk0 hkTop]

end SupercriticalLQGUniqueness.B2.DG20Lim
