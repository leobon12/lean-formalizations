/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3CollarRecords
import InteractingSLE.Spec.Supplement.SBS3CollarTransport

/-!
# Lemma S3: the upper collar is the lift's left side

Packet PROVE-T14-S3, specification p. 580. Near an interior point of a real
arc, properness and injectivity keep all other portions of the curve away.
At a positive real point the lower side is the right side, so the upper
half-disc is the left side.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.S3

/-- Near a positive real point in the interior of a real arc of a proper
curve from zero, an entire upper half-disc lies on the open left side. -/
theorem exists_upper_collar_subset_leftSide {γ : ℝ≥0 → ℂ}
    (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0)
    {a b t : ℝ≥0} (ht : t ∈ Ioo a b)
    (hreal : ∀ s ∈ Ioo a b, (γ s).im = 0) (hpos : 0 < (γ t).re) :
    ∃ ρ > 0, ball (γ t) ρ ∩ H ⊆ Supp9B.leftSide γ := by
  have h0 : (γ 0).im = 0 := by rw [hγ0]; rfl
  have hclosed : IsClosed (γ '' (Ioo a b)ᶜ) :=
    Supp9B.isClosed_image hγ isOpen_Ioo.isClosed_compl
  have hoff : γ t ∉ γ '' (Ioo a b)ᶜ := by
    rintro ⟨s, hs, hst⟩
    exact hs (hγ.2.1 hst ▸ ht)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hclosed.isOpen_compl _ hoff
  let ρ : ℝ := min δ ((γ t).re / 2)
  have hρ : 0 < ρ := lt_min hδ (half_pos hpos)
  have hρδ : ρ ≤ δ := min_le_left _ _
  have hρx : ρ ≤ (γ t).re / 2 := min_le_right _ _
  have hfree : ball (γ t) ρ ∩ H ⊆ (seedRayClosure γ)ᶜ := by
    rintro w ⟨hwb, hwH⟩ (⟨s, hsw⟩ | ⟨-, hwim⟩)
    · have hs : s ∈ Ioo a b := by
        by_contra hs
        exact hball (Metric.ball_subset_ball hρδ hwb) ⟨s, hs, hsw⟩
      have him : w.im = 0 := by rw [← hsw]; exact hreal s hs
      exact (ne_of_gt (show 0 < w.im from hwH)) him
    · rw [hγ0, Complex.zero_im] at hwim
      exact (not_lt.2 hwim) hwH
  have hcl : γ t ∈ closure (Supp9B.leftSide γ) :=
    Supp9B.seedRayClosure_subset_closure_leftSide hγ h0 (Or.inl ⟨t, rfl⟩)
  obtain ⟨w, hwL, hwd⟩ := Metric.mem_closure_iff.1 hcl ρ hρ
  have hwb : w ∈ ball (γ t) ρ := by
    rw [mem_ball, dist_comm]
    exact hwd
  have hwre : 0 < w.re := by
    have hdist : ‖γ t - w‖ < ρ := by simpa only [dist_eq_norm] using hwd
    have hre := Complex.re_le_norm (γ t - w)
    rw [Complex.sub_re] at hre
    linarith only [hre, hdist, hρx, hpos]
  have hwH : w ∈ H := by
    by_contra hw
    have hre := re_lt_of_mem_leftSide hγ h0 hwL (not_lt.1 hw)
    rw [hγ0, Complex.zero_re] at hre
    exact (not_lt.2 hwre.le) hre
  refine ⟨ρ, hρ, ?_⟩
  have hconn : IsPreconnected (ball (γ t) ρ ∩ H) :=
    ((convex_ball (γ t) ρ).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hsub := hconn.subset_connectedComponentIn ⟨hwb, hwH⟩ hfree
  rw [← connectedComponentIn_eq hwL] at hsub
  exact hsub

/-- A positive real common arc has one upper collar which is both the
lift's left side and, after mapping back, part of the joint unbounded
domain. This combines the side identification and the unused-tail access. -/
theorem exists_left_joint_collar_of_lift {A : Set ℂ} {c : Chart} {g : ℂ → ℂ}
    (hc : IsDomainChart (H \ fillH A) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hgrow : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂)
    (hAc : IsClosed A) {β γ : ℝ≥0 → ℂ} (hβ : Continuous β)
    (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) {tL a b t : ℝ≥0}
    (hpre : β '' Icc 0 tL ⊆ hullK A)
    (hlift : ∀ s, g (γ s) = β (tL + s)) (ht : t ∈ Ioo a b)
    (hreal : ∀ s ∈ Icc a b, (γ s).im = 0) (hpos : 0 < (γ t).re) :
    ∃ ρ > 0,
      g '' (ball (γ t) ρ ∩ H) ⊆ H \ fillH (A ∪ β '' Icc 0 (tL + b)) ∧
      ball (γ t) ρ ∩ H ⊆ Supp9B.leftSide γ := by
  obtain ⟨rJ, hrJ, hJ⟩ := exists_joint_collar_of_lift hc hgc hgi hC₁ hgrow
    hAc hβ hγ hpre hlift ht.1 ht.2.le hreal
  obtain ⟨rL, hrL, hL⟩ := exists_upper_collar_subset_leftSide hγ hγ0 ht
    (fun s hs => hreal s (Ioo_subset_Icc_self hs)) hpos
  refine ⟨min rJ rL, lt_min hrJ hrL, ?_, ?_⟩
  · exact (image_mono (inter_subset_inter_left H
      (Metric.ball_subset_ball (min_le_left rJ rL)))).trans hJ
  · exact (inter_subset_inter_left H
      (Metric.ball_subset_ball (min_le_right rJ rL))).trans hL

end InteractingSLE.Theorem14.SB.S3
