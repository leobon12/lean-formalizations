import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorSquare

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

private theorem laneC_convex_left_side : Convex ℝ (rectAB 1 1).side₁ := by
  have h : (rectAB 1 1).side₁ =
      (Complex.reLm ⁻¹' Icc (0 : ℝ) 0) ∩
        (Complex.imLm ⁻¹' Icc (0 : ℝ) 1) := by
    ext z
    simp only [mem_rectAB_side₁, mem_inter_iff, mem_preimage,
      mem_Icc, Complex.reLm, Complex.imLm]
    constructor
    · rintro ⟨hz, him⟩
      exact ⟨⟨hz.ge, hz.le⟩, him⟩
    · rintro ⟨hre, him⟩
      exact ⟨le_antisymm hre.2 hre.1, him⟩
  rw [h]
  exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

private theorem laneC_convex_right_side : Convex ℝ (rectAB 1 1).side₂ := by
  have h : (rectAB 1 1).side₂ =
      (Complex.reLm ⁻¹' Icc (1 : ℝ) 1) ∩
        (Complex.imLm ⁻¹' Icc (0 : ℝ) 1) := by
    ext z
    simp only [mem_rectAB_side₂, mem_inter_iff, mem_preimage,
      mem_Icc, Complex.reLm, Complex.imLm]
    constructor
    · rintro ⟨hz, him⟩
      exact ⟨⟨hz.ge, hz.le⟩, him⟩
    · rintro ⟨hre, him⟩
      exact ⟨le_antisymm hre.2 hre.1, him⟩
  rw [h]
  exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

 

theorem laneC_separator_intersects_marked_side
    {X E F S : Set ℂ} (hsep : LQGMetric.Disconnects X E F)
    (hS : Convex ℝ S) {x y : ℂ}
    (hxS : x ∈ S) (hyS : y ∈ S) (hxE : x ∈ E) (hyF : y ∈ F) :
    (X ∩ S).Nonempty := by
  have hconn : IsPathConnected S := hS.isPathConnected ⟨x, hxS⟩
  obtain ⟨γ, hγ⟩ := hconn.joinedIn x hxS y hyS
  obtain ⟨z, ⟨t, ht⟩, hzX⟩ := hsep x y γ hxE hyF
  exact ⟨z, hzX, ht ▸ hγ t⟩

private theorem laneC_left_corners_mem :
    (0 : ℂ) ∈ (rectAB 1 1).side₁ ∧
      Complex.I ∈ (rectAB 1 1).side₁ := by
  constructor <;> rw [mem_rectAB_side₁] <;> norm_num

private theorem laneC_right_corners_mem :
    (1 : ℂ) ∈ (rectAB 1 1).side₂ ∧
      (1 + Complex.I) ∈ (rectAB 1 1).side₂ := by
  constructor <;> rw [mem_rectAB_side₂] <;> norm_num

private theorem laneC_outer_of_two_corners
    (c a b : ℂ) {r : ℝ} (hr : 2 * r < 1 / 8)
    (hab : dist a b = 1) :
    2 * r < dist a c ∨ 2 * r < dist b c := by
  by_contra h
  push Not at h
  have htri := dist_triangle a c b
  rw [hab, dist_comm c b] at htri
  linarith

 

theorem laneC_separator_meets_left_side_of_inner_hit
    {X : Set ℂ} {c : ℂ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : 2 * r < 1 / 8)
    (hsep : LQGMetric.Disconnects X (sphere c r) (sphere c (2 * r)))
    {x : ℂ} (hx : x ∈ (rectAB 1 1).side₁) (hxin : dist x c ≤ r) :
    (X ∩ (rectAB 1 1).side₁).Nonempty := by
  have hcorners := laneC_left_corners_mem
  have hfar : 2 * r < dist (0 : ℂ) c ∨ 2 * r < dist Complex.I c := by
    apply laneC_outer_of_two_corners c 0 Complex.I hr
    simp [Complex.dist_eq]
  obtain ⟨y, hy, hyfar⟩ :
      ∃ y ∈ (rectAB 1 1).side₁, 2 * r < dist y c := by
    rcases hfar with h | h
    · exact ⟨0, hcorners.1, h⟩
    · exact ⟨Complex.I, hcorners.2, h⟩
  apply laneC_separator_intersects_marked_side
    (LQGMetric.Disconnects.closedBall_compl_ball (by linarith) hsep)
    laneC_convex_left_side hx hy hxin
  exact not_lt.mpr hyfar.le

 

theorem laneC_separator_meets_right_side_of_inner_hit
    {X : Set ℂ} {c : ℂ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : 2 * r < 1 / 8)
    (hsep : LQGMetric.Disconnects X (sphere c r) (sphere c (2 * r)))
    {x : ℂ} (hx : x ∈ (rectAB 1 1).side₂) (hxin : dist x c ≤ r) :
    (X ∩ (rectAB 1 1).side₂).Nonempty := by
  have hcorners := laneC_right_corners_mem
  have hfar : 2 * r < dist (1 : ℂ) c ∨ 2 * r < dist (1 + Complex.I) c := by
    apply laneC_outer_of_two_corners c 1 (1 + Complex.I) hr
    simp [Complex.dist_eq]
  obtain ⟨y, hy, hyfar⟩ :
      ∃ y ∈ (rectAB 1 1).side₂, 2 * r < dist y c := by
    rcases hfar with h | h
    · exact ⟨1, hcorners.1, h⟩
    · exact ⟨1 + Complex.I, hcorners.2, h⟩
  apply laneC_separator_intersects_marked_side
    (LQGMetric.Disconnects.closedBall_compl_ball (by linarith) hsep)
    laneC_convex_right_side hx hy hxin
  exact not_lt.mpr hyfar.le

end SupercriticalLQGUniqueness.B2.DG20Conc
