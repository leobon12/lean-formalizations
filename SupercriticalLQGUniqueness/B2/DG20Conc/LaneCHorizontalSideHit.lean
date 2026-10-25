import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSideSeparatorHit

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

private theorem laneC_horizontal_side_convex (y : ℝ) :
    Convex ℝ {z : ℂ | z.im = y ∧ 0 ≤ z.re ∧ z.re ≤ 1} := by
  have h : {z : ℂ | z.im = y ∧ 0 ≤ z.re ∧ z.re ≤ 1} =
      (Complex.imLm ⁻¹' Icc y y) ∩
        (Complex.reLm ⁻¹' Icc (0 : ℝ) 1) := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq,
      mem_Icc, Complex.reLm, Complex.imLm]
    constructor
    · rintro ⟨hy, hx₀, hx₁⟩
      exact ⟨⟨hy.ge, hy.le⟩, ⟨hx₀, hx₁⟩⟩
    · rintro ⟨hy, hx⟩
      exact ⟨le_antisymm hy.2 hy.1, hx.1, hx.2⟩
  rw [h]
  exact ((convex_Icc _ _).linear_preimage Complex.imLm).inter
    ((convex_Icc _ _).linear_preimage Complex.reLm)

private theorem laneC_horizontal_corners_far
    (c : ℂ) {r y : ℝ} (hr : 2 * r < 1 / 8) :
    2 * r < dist (Complex.I * y) c ∨
      2 * r < dist (1 + Complex.I * y) c := by
  by_contra h
  push Not at h
  have htri := dist_triangle (Complex.I * y) c (1 + Complex.I * y)
  have hdist : dist (Complex.I * y) (1 + Complex.I * y) = 1 := by
    simp
  rw [hdist, dist_comm c (1 + Complex.I * y)] at htri
  linarith

 

theorem laneC_separator_meets_horizontal_side_of_inner_hit
    {X : Set ℂ} {c x : ℂ} {r y : ℝ}
    (hr0 : 0 ≤ r) (hr : 2 * r < 1 / 8)
    (hsep : LQGMetric.Disconnects X (sphere c r) (sphere c (2 * r)))
    (hx : x ∈ {z : ℂ | z.im = y ∧ 0 ≤ z.re ∧ z.re ≤ 1})
    (hxin : dist x c ≤ r) :
    (X ∩ {z : ℂ | z.im = y ∧ 0 ≤ z.re ∧ z.re ≤ 1}).Nonempty := by
  have hfar := laneC_horizontal_corners_far c (y := y) hr
  obtain ⟨w, hw, hwfar⟩ :
      ∃ w ∈ {z : ℂ | z.im = y ∧ 0 ≤ z.re ∧ z.re ≤ 1},
        2 * r < dist w c := by
    rcases hfar with h | h
    · refine ⟨Complex.I * y, ?_, h⟩
      simp [Complex.mul_re, Complex.mul_im]
    · refine ⟨1 + Complex.I * y, ?_, h⟩
      simp [Complex.mul_re, Complex.mul_im]
  apply laneC_separator_intersects_marked_side
    (LQGMetric.Disconnects.closedBall_compl_ball (by linarith) hsep)
    (laneC_horizontal_side_convex y) hx hw hxin
  exact not_lt.mpr hwfar.le

 

theorem laneC_separator_meets_top_of_center_near
    {X : Set ℂ} {c : ℂ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : 2 * r < 1 / 8)
    (hsep : LQGMetric.Disconnects X (sphere c r) (sphere c (2 * r)))
    (hcre0 : 0 ≤ c.re) (hcre1 : c.re ≤ 1)
    (hcim : c.im ≤ 1) (hnear : 1 - c.im ≤ r) :
    (X ∩ {z : ℂ | z.im = 1 ∧ 0 ≤ z.re ∧ z.re ≤ 1}).Nonempty := by
  let x : ℂ := (c.re : ℂ) + Complex.I
  have hx : x ∈ {z : ℂ | z.im = 1 ∧ 0 ≤ z.re ∧ z.re ≤ 1} := by
    simp [x, hcre0, hcre1]
  have hdist : dist x c = 1 - c.im := by
    rw [Complex.dist_eq]
    have heq : x - c = (1 - c.im) * Complex.I := by
      apply Complex.ext <;> simp [x, Complex.mul_re, Complex.mul_im]
    rw [heq, norm_mul]
    simp only [Complex.norm_I, mul_one]
    norm_cast
    exact abs_of_nonneg (by linarith : 0 ≤ 1 - c.im)
  exact laneC_separator_meets_horizontal_side_of_inner_hit hr0 hr hsep hx
    (hdist.trans_le hnear)

 
theorem laneC_separator_meets_bottom_of_center_near
    {X : Set ℂ} {c : ℂ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : 2 * r < 1 / 8)
    (hsep : LQGMetric.Disconnects X (sphere c r) (sphere c (2 * r)))
    (hcre0 : 0 ≤ c.re) (hcre1 : c.re ≤ 1)
    (hcim : 0 ≤ c.im) (hnear : c.im ≤ r) :
    (X ∩ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1}).Nonempty := by
  let x : ℂ := (c.re : ℂ)
  have hx : x ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1} := by
    simp [x, hcre0, hcre1]
  have hdist : dist x c = c.im := by
    rw [Complex.dist_eq]
    have heq : x - c = -c.im * Complex.I := by
      apply Complex.ext <;> simp [x, Complex.mul_re, Complex.mul_im]
    rw [heq, norm_mul]
    simp only [Complex.norm_I, mul_one]
    norm_cast
    simp [abs_of_nonneg hcim]
  exact laneC_separator_meets_horizontal_side_of_inner_hit hr0 hr hsep hx
    (hdist.trans_le hnear)

end SupercriticalLQGUniqueness.B2.DG20Conc
