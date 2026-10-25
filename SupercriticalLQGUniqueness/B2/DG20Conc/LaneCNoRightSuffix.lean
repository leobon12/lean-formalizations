import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCNoLeftPrefix
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCNoRightCarrier

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

private theorem laneC_right_side_convex_local :
    Convex ℝ (rectAB 1 1).side₂ := by
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

 
theorem laneC_right_side_outer_point (c : ℂ) {r : ℝ}
    (hr : 2 * r < 1 / 8) :
    ∃ y ∈ (rectAB 1 1).side₂, 2 * r < dist y c := by
  have hzero : (1 : ℂ) ∈ (rectAB 1 1).side₂ := by
    rw [mem_rectAB_side₂]
    norm_num
  have hi : (1 + Complex.I) ∈ (rectAB 1 1).side₂ := by
    rw [mem_rectAB_side₂]
    norm_num
  by_cases h0 : 2 * r < dist (1 : ℂ) c
  · exact ⟨1, hzero, h0⟩
  refine ⟨1 + Complex.I, hi, ?_⟩
  have htri := dist_triangle (1 : ℂ) c (1 + Complex.I)
  have hdist : dist (1 : ℂ) (1 + Complex.I) = 1 := by
    simp
  rw [hdist, dist_comm c (1 + Complex.I)] at htri
  by_contra hnot
  have h0' := le_of_not_gt h0
  have hi' := le_of_not_gt hnot
  linarith

 
theorem laneC_right_side_outer_path (c x : ℂ) {r : ℝ}
    (hr : 2 * r < 1 / 8) (hx : x ∈ (rectAB 1 1).side₂) :
    ∃ y : ℂ, 2 * r < dist y c ∧
      ∃ p : Path x y, ∀ t, p t ∈ (rectAB 1 1).side₂ := by
  obtain ⟨y, hyS, hyFar⟩ := laneC_right_side_outer_point c hr
  have hconn : IsPathConnected (rectAB 1 1).side₂ :=
    laneC_right_side_convex_local.isPathConnected ⟨y, hyS⟩
  obtain ⟨p, hp⟩ := hconn.joinedIn x hx y hyS
  exact ⟨y, hyFar, p, hp⟩

 

theorem laneC_separator_hits_suffix_of_side_path
    {X E F S : Set ℂ} (hsep : LQGMetric.Disconnects X E F)
    (hno : X ∩ S = ∅)
    {y : ℂ} {γ : ℝ → ℂ} {m : ℝ}
    (hyF : y ∈ F) (hside : Path (γ 1) y)
    (hsideS : ∀ t, hside t ∈ S)
    (hm : m ∈ Icc (0 : ℝ) 1)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hmid : γ m ∈ E) :
    ∃ t ∈ Icc m (1 : ℝ), γ t ∈ X := by
  let γsuf := pathOfIcc γ hm.2
    (hγ.mono (Icc_subset_Icc hm.1 le_rfl))
  have hsepHit := hsep (γ m) y (γsuf.trans hside) hmid hyF
  obtain ⟨z, hzRange, hzX⟩ := hsepHit
  rw [Path.trans_range] at hzRange
  rcases hzRange with hzSuf | hzSide
  · obtain ⟨t, ht, htz⟩ := range_pathOfIcc_subset γ hm.2
      (hγ.mono (Icc_subset_Icc hm.1 le_rfl)) hzSuf
    exact ⟨t, ht, htz ▸ hzX⟩
  · obtain ⟨u, rfl⟩ := hzSide
    have : hside u ∈ X ∩ S := ⟨hzX, hsideS u⟩
    exact False.elim (by simpa [hno] using this)

 

theorem laneC_no_right_side_separator_hits_suffix
    {X : Set ℂ} {c : ℂ} {r : ℝ}
    (hr : 2 * r < 1 / 8)
    (hsep : LQGMetric.Disconnects X (sphere c r) (sphere c (2 * r)))
    (hno : ¬(X ∩ (rectAB 1 1).side₂).Nonempty)
    {γ : ℝ → ℂ}
    (hγside : γ 1 ∈ (rectAB 1 1).side₂)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hmid : dist (γ m) c ≤ r) :
    ∃ t ∈ Icc m (1 : ℝ), γ t ∈ X := by
  obtain ⟨y, hyS, hyFar⟩ := laneC_right_side_outer_point c hr
  have hconn : IsPathConnected (rectAB 1 1).side₂ :=
    laneC_right_side_convex_local.isPathConnected ⟨y, hyS⟩
  obtain ⟨p, hp⟩ := hconn.joinedIn (γ 1) hγside y hyS
  have hdisj : X ∩ (rectAB 1 1).side₂ = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hno
  have hr0 : 0 ≤ r := (dist_nonneg : 0 ≤ dist (γ m) c).trans hmid
  apply laneC_separator_hits_suffix_of_side_path
    (LQGMetric.Disconnects.closedBall_compl_ball (by linarith) hsep)
    hdisj (by change ¬dist y c < 2 * r; exact not_lt.mpr hyFar.le)
    p hp hm hγ
  simpa only [mem_closedBall] using hmid

end SupercriticalLQGUniqueness.B2.DG20Conc
