import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPaidSeparatingLoop
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCHorizontalSideHit

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 


theorem laneC_exists_paid_upper_left_corner_loop
    (D : ContMetric)
    {ρ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    {c v : ℂ} {r : ℝ} (hr0 : 0 < r) (hrSmall : 2 * r < 1 / 8)
    (hρann : ∀ t ∈ Icc a b,
      r < dist (ρ t) c ∧ dist (ρ t) c < 2 * r)
    (hv : 2 * r ≤ dist v c)
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b)
      (sphere c r) (sphere c (2 * r)))
    (hcre0 : 0 ≤ c.re) (hcreNear : c.re ≤ r)
    (hcim0 : 0 ≤ c.im) (hcim1 : c.im ≤ 1)
    (hTopNear : 1 - c.im ≤ r) :
    ∃ τ : ℝ → ℂ, ContinuousOn τ (Icc (0 : ℝ) 1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1,
        r < dist (τ u) c ∧ dist (τ u) c < 2 * r) ∧
      τ 0 = τ 1 ∧
      LQGMetric.Disconnects (τ '' Icc (0 : ℝ) 1)
        (sphere c r) (sphere c (2 * r)) ∧
      ((τ '' Icc (0 : ℝ) 1) ∩ (rectAB 1 1).side₁).Nonempty ∧
      ((τ '' Icc (0 : ℝ) 1) ∩
        {z : ℂ | z.im = 1 ∧ 0 ≤ z.re ∧ z.re ≤ 1}).Nonempty ∧
      D.len τ 0 1 ≤ D.len ρ a b := by
  obtain ⟨τ, hτ, hτann, hτclosed, hτsep, hτcost⟩ :=
    laneC_exists_paid_separating_loop D hab hρ hr0 hρann hv hsep
  have hx : (Complex.I * c.im) ∈ (rectAB 1 1).side₁ := by
    rw [mem_rectAB_side₁]
    simp [Complex.mul_re, Complex.mul_im, hcim0, hcim1]
  have hdist : dist (Complex.I * c.im) c = c.re := by
    rw [Complex.dist_eq]
    have heq : Complex.I * c.im - c = -(c.re : ℂ) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [heq]
    simp [abs_of_nonneg hcre0]
  have hleft := laneC_separator_meets_left_side_of_inner_hit hr0.le
    hrSmall hτsep hx (hdist.trans_le hcreNear)
  have htop := laneC_separator_meets_top_of_center_near hr0.le
    hrSmall hτsep hcre0 (by linarith : c.re ≤ 1) hcim1 hTopNear
  exact ⟨τ, hτ, hτann, hτclosed, hτsep, hleft, htop, hτcost⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
