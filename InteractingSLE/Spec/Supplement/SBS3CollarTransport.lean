/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3CollarFree
import InteractingSLE.Spec.Supplement.SB2FinHull

/-!
# Lemma S3: transporting the free collar into the joint unbounded domain

Packet PROVE-T14-S3, specification p. 580. The deterministic hull transport
is used before any assertion about a relative driver. The pre-entrance
portion is retained in `hullK A`; the rest is the image of the S2 lift.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.S3

/-- Coverage of the joint physical prefix in the old domain by the lifted
prefix. Points of the old history and the erased initial arc add no points
in that domain. -/
theorem joint_prefix_inter_subset_image_lift {A : Set ℂ} {β γ : ℝ≥0 → ℂ}
    {g : ℂ → ℂ} {tL b : ℝ≥0}
    (hpre : β '' Icc 0 tL ⊆ hullK A)
    (hlift : ∀ s, g (γ s) = β (tL + s)) :
    (A ∪ β '' Icc 0 (tL + b)) ∩ (H \ fillH A) ⊆ g '' (γ '' Icc 0 b) := by
  rintro z ⟨hzA | ⟨r, hr, rfl⟩, hzD⟩
  · exact False.elim (hzD.2 ⟨hzD.1, Or.inl (subset_closure hzA)⟩)
  · have hrt : tL < r := by
      by_contra h
      rcases hpre ⟨r, ⟨zero_le, not_lt.1 h⟩, rfl⟩ with hfill | ⟨x, -, hx⟩
      · exact hzD.2 hfill
      · have him : (β r).im = 0 := by rw [← hx]; exact Complex.ofReal_im x
        exact (ne_of_gt (show 0 < (β r).im from hzD.1)) him
    refine ⟨γ (r - tL), ⟨r - tL, ⟨zero_le, ?_⟩, rfl⟩, ?_⟩
    · exact (tsub_le_iff_right).2 (by simpa only [add_comm] using hr.2)
    · rw [hlift, add_tsub_cancel_of_le hrt.le]

/-- An old-chart inverse sends the unbounded domain of the lifted prefix
into the joint physical unbounded domain. This is the contrapositive of the
existing deterministic hull-transport theorem. -/
theorem inv_mem_joint_domain_of_lift {A : Set ℂ} {c : Chart} {g : ℂ → ℂ}
    (hc : IsDomainChart (H \ fillH A) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hgrow : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂)
    (hAc : IsClosed A) {β γ : ℝ≥0 → ℂ} (hβ : Continuous β)
    (hγ : Supp9B.IsProperCurve γ) {tL b : ℝ≥0}
    (hpre : β '' Icc 0 tL ⊆ hullK A)
    (hlift : ∀ s, g (γ s) = β (tL + s)) {w : ℂ}
    (hw : w ∈ H \ fillH (γ '' Icc 0 b)) :
    g w ∈ H \ fillH (A ∪ β '' Icc 0 (tL + b)) := by
  rw [hgi hw.1]
  have hwD := hc.inv_mem hw.1
  refine ⟨hwD.1, fun hfill => ?_⟩
  have h := FinRel.fwd_mem_fillH_of_mem_fillH hc hgc hgi hC₁ hgrow
    (hAc.union (isCompact_Icc.image hβ).isClosed)
    (isCompact_Icc.image hγ.1).isClosed
    (by rintro _ ⟨s, -, rfl⟩; exact hγ.2.2.1 s)
    (joint_prefix_inter_subset_image_lift hpre hlift) hfill hwD.2
  rw [hc.fwd_inv hw.1] at h
  exact hw.2 h

/-- The upper half-disc along a real lifted suffix maps entirely into the
joint unbounded domain, even when its physical landing lies in the old
history. No law or relative clock is part of this statement. -/
theorem exists_joint_collar_of_lift {A : Set ℂ} {c : Chart} {g : ℂ → ℂ}
    (hc : IsDomainChart (H \ fillH A) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hgrow : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂)
    (hAc : IsClosed A) {β γ : ℝ≥0 → ℂ} (hβ : Continuous β)
    (hγ : Supp9B.IsProperCurve γ) {tL a b t : ℝ≥0}
    (hpre : β '' Icc 0 tL ⊆ hullK A)
    (hlift : ∀ s, g (γ s) = β (tL + s))
    (hat : a < t) (htb : t ≤ b) (hreal : ∀ s ∈ Icc a b, (γ s).im = 0) :
    ∃ ρ > 0, g '' (ball (γ t) ρ ∩ H) ⊆
      H \ fillH (A ∪ β '' Icc 0 (tL + b)) := by
  obtain ⟨ρ, hρ, hfree⟩ := isFreeAt_of_real_suffix hγ hat htb hreal
  exact ⟨ρ, hρ, fun _ ⟨w, hw, he⟩ => he ▸
    inv_mem_joint_domain_of_lift hc hgc hgi hC₁ hgrow hAc hβ hγ hpre hlift (hfree hw)⟩

end InteractingSLE.Theorem14.SB.S3
