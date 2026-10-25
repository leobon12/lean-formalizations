import SupercriticalLQGUniqueness.B2.DG20Lim.RationalAnnulusBuffer

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem centeredRatAnnulus_good_of_local_lfpp_compare
    (ξ : ℝ) (φ ψ : C(ℂ, ℝ)) (x y r : ℚ) (hr : 0 < r)
    (k C : ℝ≥0∞) (hk0 : k ≠ 0) (hkTop : k ≠ ∞)
    (hψφ : ∀ u v : bufferedCenteredAnnulus x y r,
      lfppDOn ξ ψ (bufferedCenteredAnnulus x y r) u v ≤
        k * lfppDOn ξ φ (bufferedCenteredAnnulus x y r) u v)
    (hφψ : ∀ u v : bufferedCenteredAnnulus x y r,
      lfppDOn ξ φ (bufferedCenteredAnnulus x y r) u v ≤
        k * lfppDOn ξ ψ (bufferedCenteredAnnulus x y r) u v)
    (hgood : (lfppContMetric ξ φ φ.continuous).aroundDist
        (centeredRatAnnulus x y r hr).toSet
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet ≤
      C * setDist (lfppContMetric ξ φ φ.continuous)
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet) :
    (lfppContMetric ξ ψ ψ.continuous).aroundDist
        (centeredRatAnnulus x y r hr).toSet
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet ≤
      (k * C * k) * setDist (lfppContMetric ξ ψ ψ.continuous)
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet := by
  let c : ℂ := Complex.mk (x : ℝ) (y : ℝ)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hρ : (r : ℝ) < 2 * (r : ℝ) := by linarith
  have hAround := lfppAroundDist_le_mul_of_lfppDOn_le ξ φ ψ
    (bufferedCenteredAnnulus x y r)
    (centeredRatAnnulus x y r hr).toSet
    (centeredInnerCircle x y r hr).toSet
    (centeredOuterCircle x y r hr).toSet
    (bufferedCenteredAnnulus x y r).isOpen
    (centeredRatAnnulus_subset_buffered x y r hr)
    k hk0 hkTop hψφ
  have hCircle := lfppCircleSetDist_le_mul_of_lfppDOn_le ξ ψ φ
    (bufferedCenteredAnnulus x y r) (bufferedCenteredAnnulus x y r).isOpen
    c (r : ℝ) (2 * (r : ℝ)) hρ
    (centered_shell_subset_buffered x y r hr)
    k hk0 hkTop hφψ
  have hCircle' : setDist (lfppContMetric ξ φ φ.continuous)
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet ≤
      k * setDist (lfppContMetric ξ ψ ψ.continuous)
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet := by
    simpa [RatCircle.toSet, RatCircle.center, centeredInnerCircle,
      centeredOuterCircle, c, mul_comm] using hCircle
  calc
    (lfppContMetric ξ ψ ψ.continuous).aroundDist
        (centeredRatAnnulus x y r hr).toSet
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet
      ≤ k * (lfppContMetric ξ φ φ.continuous).aroundDist
          (centeredRatAnnulus x y r hr).toSet
          (centeredInnerCircle x y r hr).toSet
          (centeredOuterCircle x y r hr).toSet := hAround
    _ ≤ k * (C * setDist (lfppContMetric ξ φ φ.continuous)
          (centeredInnerCircle x y r hr).toSet
          (centeredOuterCircle x y r hr).toSet) := by gcongr
    _ ≤ k * (C * (k * setDist (lfppContMetric ξ ψ ψ.continuous)
          (centeredInnerCircle x y r hr).toSet
          (centeredOuterCircle x y r hr).toSet)) := by gcongr
    _ = (k * C * k) * setDist (lfppContMetric ξ ψ ψ.continuous)
          (centeredInnerCircle x y r hr).toSet
          (centeredOuterCircle x y r hr).toSet := by simp only [mul_assoc]

end SupercriticalLQGUniqueness.B2.DG20Lim
