import SupercriticalLQGUniqueness.B2.DG20Lim.AroundCostInternalCompare

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem lfppAroundDist_le_mul_of_lfppDOn_le
    (ξ : ℝ) (φ ψ : C(ℂ, ℝ))
    (V A B C : Set ℂ) (hV : IsOpen V) (hAV : A ⊆ V)
    (k : ℝ≥0∞) (hk0 : k ≠ 0) (hkTop : k ≠ ∞)
    (hcmp : ∀ x y : V, lfppDOn ξ ψ V x y ≤ k * lfppDOn ξ φ V x y) :
    (lfppContMetric ξ ψ ψ.continuous).aroundDist A B C ≤
      k * (lfppContMetric ξ φ φ.continuous).aroundDist A B C := by
  apply aroundDist_le_mul_of_internal_le
    (lfppContMetric ξ φ φ.continuous) (lfppContMetric ξ ψ ψ.continuous)
    V A B C hAV k hk0 hkTop
  intro z hz w hw
  simpa only [lfppContMetric_internal_eq_lfppDOn ξ ψ hV ⟨z, hz⟩ ⟨w, hw⟩,
    lfppContMetric_internal_eq_lfppDOn ξ φ hV ⟨z, hz⟩ ⟨w, hw⟩] using
      hcmp ⟨z, hz⟩ ⟨w, hw⟩

theorem lfppCircleSetDist_le_mul_of_lfppDOn_le
    (ξ : ℝ) (φ ψ : C(ℂ, ℝ))
    (V : Set ℂ) (hV : IsOpen V) (z : ℂ) (ρ₁ ρ₂ : ℝ) (hρ : ρ₁ < ρ₂)
    (hsub : ∀ w : ℂ, ρ₁ ≤ ‖w - z‖ → ‖w - z‖ ≤ ρ₂ → w ∈ V)
    (k : ℝ≥0∞) (hk0 : k ≠ 0) (hkTop : k ≠ ∞)
    (hcmp : ∀ x y : V, lfppDOn ξ ψ V x y ≤ k * lfppDOn ξ φ V x y) :
    setDist (lfppContMetric ξ ψ ψ.continuous)
      (Metric.sphere z ρ₁) (Metric.sphere z ρ₂) ≤
      k * setDist (lfppContMetric ξ φ φ.continuous)
        (Metric.sphere z ρ₁) (Metric.sphere z ρ₂) := by
  apply setDist_spheres_le_mul_of_internal_le
    (lfppContMetric ξ φ φ.continuous) (lfppContMetric ξ ψ ψ.continuous)
    (isLength_lfppContMetric φ.continuous) (isLength_lfppContMetric ψ.continuous)
    V z ρ₁ ρ₂ hρ hsub k hk0 hkTop
  intro x hx y hy
  have hxV : x ∈ V := by
    apply hsub x
    · simpa only [dist_eq_norm] using (Metric.mem_sphere.mp hx).ge
    · simpa only [dist_eq_norm] using (Metric.mem_sphere.mp hx).le.trans hρ.le
  have hyV : y ∈ V := by
    apply hsub y
    · simpa only [dist_eq_norm] using hρ.le.trans (Metric.mem_sphere.mp hy).ge
    · simpa only [dist_eq_norm] using (Metric.mem_sphere.mp hy).le
  simpa only [lfppContMetric_internal_eq_lfppDOn ξ ψ hV ⟨x, hxV⟩ ⟨y, hyV⟩,
    lfppContMetric_internal_eq_lfppDOn ξ φ hV ⟨x, hxV⟩ ⟨y, hyV⟩] using
      hcmp ⟨x, hxV⟩ ⟨y, hyV⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
