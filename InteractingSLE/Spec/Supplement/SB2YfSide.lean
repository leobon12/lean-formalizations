/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewTransport
import InteractingSLE.Spec.Supplement.SB2FinCollar
import InteractingSLE.Spec.Supplement.SB2JRight

/-!
# S1 in stage coordinates from the relative picture (head time `0`)

Packet PROVE-T14-SB2LIFT (round 32; `IsStageS2`'s S1 clause). SB4's transport `image_closedRightSide_of_actual_tail`
(the closed right side of the relative curve `γ` is carried by the boundary map `g` into the closed right side of the
actual curve `β = g ∘ γ(t_L + ·)`) takes S1 for the retained path as a hypothesis, but reads it only through the head
`β([0, t_L]) ⊆ K_p`. At head time `t_L = 0` the head is `{0} ⊆ K_p`, so:

* **`image_closedRightSide_of_tail_zero`**: the transport at `t_L = 0`, without S1;
* **`subset_closedRightSide_of_arc`**: a retained path read on the nonnegative relative axis (`p(s) = g(K s)`) lies on
  the closed right side of `β` — S1 itself, from the relative picture.
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B

namespace InteractingSLE.Theorem14.SB.Sx

/-- **SB4's transport at head time `0`, without S1.** -/
theorem image_closedRightSide_of_tail_zero {p : ℝ → ℂ} {β γ : ℝ≥0 → ℂ} {c : Chart} {g : ℂ → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hβ : IsProperCurve β) (hβ0 : β 0 = 0)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (htail : ∀ s, g (γ s) = β (0 + s))
    (hfree : ∃ x : ℝ, 0 < x ∧ realMax (p '' Icc 0 1) < x ∧ (x : ℂ) ∉ range β) :
    g '' (closedRightSide γ ∩ {z | 0 ≤ z.im}) ⊆ closedRightSide β := by
  have hglue := gluedCurve_eq_of_actual_tail htail
  have hΓ : IsProperCurve (gluedCurve β g γ 0) := by rw [hglue]; exact hβ
  have hΓ0 : gluedCurve β g γ 0 0 = 0 := by rw [hglue, hβ0]
  have hAc : IsCompact (p '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hp
  have h0A : ((0 : ℝ) : ℂ) ∈ p '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hp0, Complex.ofReal_zero]⟩
  have hhead : β '' Icc 0 0 ⊆ hullK (p '' Icc 0 1) := by
    rintro _ ⟨r, hr, rfl⟩
    have hr0 : r = 0 := le_antisymm hr.2 bot_le
    rw [hr0, hβ0]
    refine Or.inr ⟨0, ⟨FinRel.realMin_le_of_mem hAc h0A, Lx.le_realMax_of_mem hAc h0A⟩, by simp⟩
  have hoff : ∀ w ∈ H, w ∉ range γ → g w ∉ seedRayClosure β := by
    intro w hw hwγ
    rw [← hglue]
    exact s5_inv_notMem_glued hc.1 hgc hgi hhead hγ hΓ0 hw hwγ
  have hleft : g '' (leftSide γ ∩ H) ⊆ leftSide β := by
    rw [← hglue]
    exact s5_left_transport_of_negative_gates hγ hγ0 hΓ hgc
      (fun w hw => by rw [hglue]; exact hoff w hw.2 (notMem_range_of_mem_leftSide hw.1))
      (fun x hx hxγ => s5_negative_gate_image hp hp0 hc hgc hgi hhead hγ hΓ hΓ0 hx hxγ)
  obtain ⟨x, hx, hxR, hxβ⟩ := hfree
  have hanchor := exists_right_anchor_of_actual_free_real hp hp0 hβ hβ0 hc hgi hx hxR hxβ
  have hright := s5_right_transport_of_left hc.1 hgi (hgc.mono H_subset_im_nonneg)
    hγ hγ0 hβ hβ0 (fun s _ => Or.inl ⟨0 + s, (htail s).symm⟩) hoff hleft hanchor
  apply s5_image_right_upper_of_interior hγ hγ0 hβ hβ0 hgc
  · intro t
    rw [htail]
    exact Or.inr (Or.inl (mem_range_self _))
  · intro w hw
    exact Or.inl (hright ⟨w, hw, rfl⟩)

/-- **S1 from the relative picture**: a retained path read on the nonnegative relative axis lies on the closed right
side of `β = g ∘ γ`. -/
theorem subset_closedRightSide_of_arc {p : ℝ → ℂ} {β γ : ℝ≥0 → ℂ} {c : Chart} {g : ℂ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hpg : ∀ s ∈ Icc (0 : ℝ) 1, p s = g ((K * s : ℝ) : ℂ))
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hβ : IsProperCurve β) (hβ0 : β 0 = 0)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (htail : ∀ s, g (γ s) = β s)
    (hfree : ∃ x : ℝ, 0 < x ∧ realMax (p '' Icc 0 1) < x ∧ (x : ℂ) ∉ range β) :
    p '' Icc 0 1 ⊆ closedRightSide β := by
  have htail' : ∀ s, g (γ s) = β (0 + s) := fun s => by rw [zero_add]; exact htail s
  have htr := image_closedRightSide_of_tail_zero hp hp0 hβ hβ0 hc hgc hgi hγ hγ0 htail' hfree
  rintro _ ⟨s, hs, rfl⟩
  rw [hpg s hs]
  refine htr ⟨((K * s : ℝ) : ℂ), ⟨?_, by simp⟩, rfl⟩
  have hx0 : 0 ≤ K * s := mul_nonneg hK hs.1
  by_cases hmem : ((K * s : ℝ) : ℂ) ∈ seedRayClosure γ
  · exact Or.inr hmem
  · rcases hx0.lt_or_eq with hlt | heq
    · exact Or.inl (ofReal_mem_rightSide hγ hγ0 hlt fun h => hmem (Or.inl h))
    · exact absurd (Or.inl ⟨0, by rw [hγ0, ← heq, Complex.ofReal_zero]⟩) hmem

end InteractingSLE.Theorem14.SB.Sx
