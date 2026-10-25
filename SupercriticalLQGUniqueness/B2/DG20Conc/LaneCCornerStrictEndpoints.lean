import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerPaidCrosscutOriented

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_left_contact_strictly_below
    {z c : ℂ} {r : ℝ}
    (hz : z.re = 0) (hbelow : z.im ≤ c.im)
    (hc0 : 0 ≤ c.re) (hcNear : c.re ≤ r)
    (hinner : r < dist z c) : z.im < c.im := by
  rcases hbelow.eq_or_lt with heq | hlt
  · have hsq : ‖z - c‖ ^ 2 =
        (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im]
      ring
    rw [hz, heq] at hsq
    have hn : r < ‖z - c‖ := by simpa [dist_eq_norm] using hinner
    nlinarith [norm_nonneg (z - c)]
  · exact hlt

 

theorem laneC_top_contact_strictly_right
    {z c : ℂ} {r : ℝ}
    (hz : z.im = 1) (hright : c.re ≤ z.re)
    (hc1 : c.im ≤ 1) (hcNear : 1 - c.im ≤ r)
    (hinner : r < dist z c) : c.re < z.re := by
  rcases hright.eq_or_lt with heq | hlt
  · have hsq : ‖z - c‖ ^ 2 =
        (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im]
      ring
    rw [heq, hz] at hsq
    have hn : r < ‖z - c‖ := by simpa [dist_eq_norm] using hinner
    nlinarith [norm_nonneg (z - c)]
  · exact hlt

 

theorem laneC_upper_left_paid_square_crosscut_strict
    (D : ContMetric) {ρ : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hρ : ContinuousOn ρ (Icc a b))
    {c v : ℂ} {r : ℝ} (hr : 0 < r)
    (hρann : ∀ x ∈ Icc a b,
      r < dist (ρ x) c ∧ dist (ρ x) c < 2 * r)
    (hv : 2 * r ≤ dist v c)
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b)
      (sphere c r) (sphere c (2 * r)))
    (hcre0 : 0 ≤ c.re) (hcreNear : c.re ≤ r)
    (hcim1 : c.im ≤ 1) (hTopNear : 1 - c.im ≤ r)
    (hbelow : 2 * r ≤ c.im) (hright : c.re + 2 * r ≤ 1) :
    ∃ α : ℝ → ℂ,
      ContinuousOn α (Icc (0 : ℝ) 1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1,
        r < dist (α u) c ∧ dist (α u) c < 2 * r ∧
          α u ∈ (rectAB 1 1).toSet) ∧
      α 0 ∈ (rectAB 1 1).side₁ ∧
      (α 1).im = 1 ∧
      (α 0).im < c.im ∧ c.re < (α 1).re ∧
      D.len α 0 1 ≤ D.len ρ a b := by
  obtain ⟨α, hα, hαann, hαleft, hαtop, hαbelow, hαright, hcost⟩ :=
    laneC_upper_left_paid_square_crosscut_oriented D hab hρ hr hρann hv hsep
      hcre0 hcreNear hcim1 hTopNear hbelow hright
  have hleftre : (α 0).re = 0 := (mem_rectAB_side₁.mp hαleft).1
  have hα0inner := (hαann 0 (by simp)).1
  have hα1inner := (hαann 1 (by simp)).1
  exact ⟨α, hα, hαann, hαleft, hαtop,
    laneC_left_contact_strictly_below hleftre hαbelow hcre0 hcreNear hα0inner,
    laneC_top_contact_strictly_right hαtop hαright hcim1 hTopNear hα1inner,
    hcost⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
