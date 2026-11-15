/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3CollarTransport

/-!
# Lemma S3: the old-to-joint transition has a real gap

Packet PROVE-T14-S3, specification p. 580. The free upper half-disc supplied
by the unused proper tail gives a full ball disjoint from the transition
hull: that hull lies in the open half-plane. The deterministic hull
transport supplies its inclusion in the lifted filling.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.S3

/-- The lifted old-to-joint hull increment avoids a full ball at a real
suffix point compared before the retained cut. -/
theorem exists_ball_disjoint_joint_transition_of_lift
    {A : Set ℂ} {c : Chart} {g : ℂ → ℂ}
    (hc : IsDomainChart (H \ fillH A) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hgrow : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂)
    (hAc : IsClosed A) {β γ : ℝ≥0 → ℂ} (hβ : Continuous β)
    (hγ : Supp9B.IsProperCurve γ) {tL a b t : ℝ≥0}
    (hpre : β '' Icc 0 tL ⊆ hullK A)
    (hlift : ∀ s, g (γ s) = β (tL + s))
    (hat : a < t) (htb : t ≤ b) (hreal : ∀ s ∈ Icc a b, (γ s).im = 0) :
    ∃ ρ > 0, Disjoint (ball (γ t) ρ)
      (c.1 '' (fillH (A ∪ β '' Icc 0 (tL + b)) \ fillH A)) := by
  obtain ⟨ρ, hρ, hfree⟩ := isFreeAt_of_real_suffix hγ hat htb hreal
  refine ⟨ρ, hρ, Set.disjoint_left.2 ?_⟩
  rintro w hwb ⟨z, ⟨hzB, hzA⟩, hzw⟩
  have hwH := hc.fwd_mem ⟨hzB.1, hzA⟩
  have hfill := FinRel.fwd_mem_fillH_of_mem_fillH hc hgc hgi hC₁ hgrow
    (hAc.union (isCompact_Icc.image hβ).isClosed)
    (isCompact_Icc.image hγ.1).isClosed
    (by rintro _ ⟨s, -, rfl⟩; exact hγ.2.2.1 s)
    (joint_prefix_inter_subset_image_lift hpre hlift) hzB hzA
  rw [hzw] at hwH hfill
  exact (hfree ⟨hwb, hwH⟩).2 hfill

end InteractingSLE.Theorem14.SB.S3
