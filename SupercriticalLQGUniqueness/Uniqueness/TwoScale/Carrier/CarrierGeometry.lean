import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.DyadicSample




set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

 
theorem small_annulus_subset_carrier
    {R l : ℝ} (hR : 0 < R) (hl : 0 < l) (hl1 : l < 1)
    (z₀ x : ℂ)
    (hcorelo : 3 * R / 4 ≤ dist x z₀)
    (hcorehi : dist x z₀ ≤ 3 * R / 2)
    (hradius : l ^ ((3 : ℝ) / 4) * R ≤ R / 8) :
    (annulusAt x (l * R) (l ^ ((3 : ℝ) / 4) * R)
      (mul_pos hl hR)
      (mul_lt_mul_of_pos_right
        (Real.self_lt_rpow_of_lt_one hl hl1 (by norm_num)) hR)).toSet ⊆
        closedBall z₀ (2 * R) \ ball z₀ (R / 2) := by
  intro w hw
  have hw' := hw
  rw [EuclideanAnnulus.toSet_eq] at hw'
  have hwout : dist w x < l ^ ((3 : ℝ) / 4) * R := by
    simpa only [annulusAt, EuclideanAnnulus.center, EuclideanAnnulus.outerRadius, mem_ball] using hw'.2
  have ht₁ := dist_triangle w x z₀
  have ht₂ := dist_triangle x w z₀
  rw [dist_comm x w] at ht₂
  rw [mem_sdiff, mem_closedBall, mem_ball, not_lt]
  constructor <;> linarith

 

theorem carrier_boundary_far
    {R : ℝ} (hR : 0 < R) (z₀ x y : ℂ)
    (hcorelo : 3 * R / 4 ≤ dist x z₀)
    (hcorehi : dist x z₀ ≤ 3 * R / 2)
    (hy : dist y z₀ = R / 2 ∨ dist y z₀ = 2 * R) :
    R / 4 ≤ dist y x := by
  rcases hy with hy | hy
  · have ht := dist_triangle x y z₀
    rw [dist_comm x y, hy] at ht
    linarith
  · have ht := dist_triangle y x z₀
    rw [hy] at ht
    linarith

 

theorem dyadic_outer_radius_le_eighth
    {q R : ℝ} (hq : 0 < q) (hR : 0 < R)
    (hqrad : q ^ ((3 : ℝ) / 4) ≤ 1 / 8) (n : ℕ) :
    (dyadicScale q n) ^ ((3 : ℝ) / 4) * R ≤ R / 8 := by
  have hlq := dyadicScale_le hq.le n
  have hpow := Real.rpow_le_rpow (dyadicScale_pos hq n).le hlq
    (by norm_num : (0 : ℝ) ≤ 3 / 4)
  nlinarith [mul_le_mul_of_nonneg_right (hpow.trans hqrad) hR.le]


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
