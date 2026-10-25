import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalAnnulusBuffer

 




set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem centeredRatAnnulus_good_of_local_lfpp_compareR32
    (ξ : ℝ) (φ ψ : C(ℂ, ℝ)) (x y r : ℚ) (hr : 0 < r)
    (k C : ℝ≥0∞) (hk0 : k ≠ 0) (hkTop : k ≠ ∞)
    (hψφ : ∀ u v : bufferedCenteredAnnulusR32 x y r,
      lfppDOn ξ ψ (bufferedCenteredAnnulusR32 x y r) u v ≤
        k * lfppDOn ξ φ (bufferedCenteredAnnulusR32 x y r) u v)
    (hφψ : ∀ u v : bufferedCenteredAnnulusR32 x y r,
      lfppDOn ξ φ (bufferedCenteredAnnulusR32 x y r) u v ≤
        k * lfppDOn ξ ψ (bufferedCenteredAnnulusR32 x y r) u v)
    (hgood : (lfppContMetric ξ φ φ.continuous).aroundDist
        (centeredRatAnnulusR32 x y r hr).toSet
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet ≤
      C * setDist (lfppContMetric ξ φ φ.continuous)
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet) :
    (lfppContMetric ξ ψ ψ.continuous).aroundDist
        (centeredRatAnnulusR32 x y r hr).toSet
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet ≤
      (k * C * k) * setDist (lfppContMetric ξ ψ ψ.continuous)
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet := by
  let c : ℂ := Complex.mk (x : ℝ) (y : ℝ)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hρ : (r : ℝ) < 3 / 2 * (r : ℝ) := by linarith
  have hAround := lfppAroundDist_le_mul_of_lfppDOn_le ξ φ ψ
    (bufferedCenteredAnnulusR32 x y r)
    (centeredRatAnnulusR32 x y r hr).toSet
    (centeredInnerCircleR32 x y r hr).toSet
    (centeredOuterCircleR32 x y r hr).toSet
    (bufferedCenteredAnnulusR32 x y r).isOpen
    (centeredRatAnnulus_subset_bufferedR32 x y r hr)
    k hk0 hkTop hψφ
  have hCircle := lfppCircleSetDist_le_mul_of_lfppDOn_le ξ ψ φ
    (bufferedCenteredAnnulusR32 x y r) (bufferedCenteredAnnulusR32 x y r).isOpen
    c (r : ℝ) (3 / 2 * (r : ℝ)) hρ
    (centered_shell_subset_bufferedR32 x y r hr)
    k hk0 hkTop hφψ
  have hCircle' : setDist (lfppContMetric ξ φ φ.continuous)
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet ≤
      k * setDist (lfppContMetric ξ ψ ψ.continuous)
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet := by
    simpa [RatCircle.toSet, RatCircle.center, centeredInnerCircleR32,
      centeredOuterCircleR32, c, mul_comm] using hCircle
  calc
    (lfppContMetric ξ ψ ψ.continuous).aroundDist
        (centeredRatAnnulusR32 x y r hr).toSet
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet
      ≤ k * (lfppContMetric ξ φ φ.continuous).aroundDist
          (centeredRatAnnulusR32 x y r hr).toSet
          (centeredInnerCircleR32 x y r hr).toSet
          (centeredOuterCircleR32 x y r hr).toSet := hAround
    _ ≤ k * (C * setDist (lfppContMetric ξ φ φ.continuous)
          (centeredInnerCircleR32 x y r hr).toSet
          (centeredOuterCircleR32 x y r hr).toSet) := by gcongr
    _ ≤ k * (C * (k * setDist (lfppContMetric ξ ψ ψ.continuous)
          (centeredInnerCircleR32 x y r hr).toSet
          (centeredOuterCircleR32 x y r hr).toSet)) := by gcongr
    _ = (k * C * k) * setDist (lfppContMetric ξ ψ ψ.continuous)
          (centeredInnerCircleR32 x y r hr).toSet
          (centeredOuterCircleR32 x y r hr).toSet := by simp only [mul_assoc]

end SupercriticalLQGUniqueness.B2.DG20Lim
