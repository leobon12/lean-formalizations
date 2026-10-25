import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodCostCompare
import SupercriticalLQGUniqueness.B2.DG20Pt.HeatLocalApprox

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem isBounded_bufferedCenteredAnnulus (x y r : ℚ) :
    Bornology.IsBounded (bufferedCenteredAnnulus x y r : Set ℂ) := by
  apply (isBounded_ball : Bornology.IsBounded
    (ball (Complex.mk (x : ℝ) (y : ℝ)) (4 * (r : ℝ)))).subset
  intro w hw
  change dist w (Complex.mk (x : ℝ) (y : ℝ)) < 4 * (r : ℝ)
  simpa only [dist_eq_norm] using hw.2

theorem centeredRatAnnulus_good_local_of_heat_compare
    (ξ : ℝ) (ε : Ioi (0 : ℝ)) (g : DistC) (φ : C(ℂ, ℝ))
    (hφ : ∀ z, φ z = heatMollify (ε : ℝ) g z)
    (x y r : ℚ) (hr : 0 < r) (C : ℝ≥0∞)
    (hcmp : ∀ z w : ℂ,
      lfppLocOn ξ (ε : ℝ) ε.property g (bufferedCenteredAnnulus x y r) z w ≤
        ENNReal.ofReal 2 *
          lfppDOn ξ (heatMollify (ε : ℝ) g) (bufferedCenteredAnnulus x y r) z w ∧
      lfppDOn ξ (heatMollify (ε : ℝ) g) (bufferedCenteredAnnulus x y r) z w ≤
        ENNReal.ofReal 2 *
          lfppLocOn ξ (ε : ℝ) ε.property g (bufferedCenteredAnnulus x y r) z w)
    (hgood : (lfppContMetric ξ φ φ.continuous).aroundDist
        (centeredRatAnnulus x y r hr).toSet
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet ≤
      C * setDist (lfppContMetric ξ φ φ.continuous)
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet) :
    (lfppContMetric ξ (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
        (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g).continuous).aroundDist
        (centeredRatAnnulus x y r hr).toSet
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet ≤
      (ENNReal.ofReal 2 * C * ENNReal.ofReal 2) *
        setDist (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g).continuous)
          (centeredInnerCircle x y r hr).toSet
          (centeredOuterCircle x y r hr).toSet := by
  have hφeq : (φ : ℂ → ℝ) = heatMollify (ε : ℝ) g := funext hφ
  apply centeredRatAnnulus_good_of_local_lfpp_compare ξ φ
    (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
    x y r hr (ENNReal.ofReal 2) C (by norm_num) ENNReal.ofReal_ne_top
  · intro u v
    change lfppLocOn ξ (ε : ℝ) ε.property g
      (bufferedCenteredAnnulus x y r) u v ≤
        ENNReal.ofReal 2 * lfppDOn ξ φ (bufferedCenteredAnnulus x y r) u v
    rw [hφeq]
    exact (hcmp u v).1
  · intro u v
    change lfppDOn ξ φ (bufferedCenteredAnnulus x y r) u v ≤
      ENNReal.ofReal 2 * lfppLocOn ξ (ε : ℝ) ε.property g
        (bufferedCenteredAnnulus x y r) u v
    rw [hφeq]
    exact (hcmp u v).2
  · exact hgood

end SupercriticalLQGUniqueness.B2.DG20Lim
