import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSideToInnerHit

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

private theorem laneC_left_side_convex_local :
    Convex ℝ (rectAB 1 1).side₁ := by
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

 
theorem laneC_left_side_outer_point (c : ℂ) {r : ℝ}
    (hr : 2 * r < 1 / 8) :
    ∃ y ∈ (rectAB 1 1).side₁, 2 * r < dist y c := by
  have hzero : (0 : ℂ) ∈ (rectAB 1 1).side₁ := by
    rw [mem_rectAB_side₁]
    norm_num
  have hi : Complex.I ∈ (rectAB 1 1).side₁ := by
    rw [mem_rectAB_side₁]
    norm_num
  by_cases h0 : 2 * r < dist (0 : ℂ) c
  · exact ⟨0, hzero, h0⟩
  refine ⟨Complex.I, hi, ?_⟩
  have htri := dist_triangle (0 : ℂ) c Complex.I
  have hdist : dist (0 : ℂ) Complex.I = 1 := by
    simp [Complex.dist_eq]
  rw [hdist, dist_comm c Complex.I] at htri
  by_contra hnot
  have h0' := le_of_not_gt h0
  have hi' := le_of_not_gt hnot
  linarith

 

theorem laneC_left_side_outer_path (c x : ℂ) {r : ℝ}
    (hr : 2 * r < 1 / 8) (hx : x ∈ (rectAB 1 1).side₁) :
    ∃ y : ℂ, 2 * r < dist y c ∧
      ∃ p : Path y x, ∀ t, p t ∈ (rectAB 1 1).side₁ := by
  obtain ⟨y, hyS, hyFar⟩ := laneC_left_side_outer_point c hr
  have hconn : IsPathConnected (rectAB 1 1).side₁ :=
    laneC_left_side_convex_local.isPathConnected ⟨y, hyS⟩
  obtain ⟨p, hp⟩ := hconn.joinedIn y hyS x hx
  exact ⟨y, hyFar, p, hp⟩

 

theorem laneC_no_left_side_separator_hits_prefix
    {X : Set ℂ} {c : ℂ} {r : ℝ}
    (hr : 2 * r < 1 / 8)
    (hsep : LQGMetric.Disconnects X (sphere c r) (sphere c (2 * r)))
    (hno : ¬(X ∩ (rectAB 1 1).side₁).Nonempty)
    {γ : ℝ → ℂ}
    (hγside : γ 0 ∈ (rectAB 1 1).side₁)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hmid : dist (γ m) c ≤ r) :
    ∃ t ∈ Icc (0 : ℝ) m, γ t ∈ X := by
  obtain ⟨y, hyS, hyFar⟩ := laneC_left_side_outer_point c hr
  have hconn : IsPathConnected (rectAB 1 1).side₁ :=
    laneC_left_side_convex_local.isPathConnected ⟨y, hyS⟩
  obtain ⟨p, hp⟩ := hconn.joinedIn y hyS (γ 0) hγside
  have hdisj : X ∩ (rectAB 1 1).side₁ = ∅ := by
    exact Set.not_nonempty_iff_eq_empty.mp hno
  have hr0 : 0 ≤ r := (dist_nonneg : 0 ≤ dist (γ m) c).trans hmid
  apply laneC_separator_hits_prefix_of_side_path
    (LQGMetric.Disconnects.closedBall_compl_ball (by linarith) hsep)
    hdisj (by change ¬dist y c < 2 * r; exact not_lt.mpr hyFar.le)
    p hp hm hγ
  simpa only [mem_closedBall] using hmid

end SupercriticalLQGUniqueness.B2.DG20Conc
