/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewSides

/-!
# Physical sewing along the complete actual tail

S5 applies to the actual proper curve itself as its own completion. Exact
correspondence of the whole lifted tail identifies the glued curve with that
actual curve. Thus the new relative closed-side comparison transports through
the boundary extension, and the old history keeps its previous side.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B

namespace InteractingSLE.Theorem14.SB

/-- Sewing an exact lift of the complete tail restores the actual curve. -/
theorem gluedCurve_eq_of_actual_tail {β γ : ℝ≥0 → ℂ} {g : ℂ → ℂ} {tL : ℝ≥0}
    (htail : ∀ s, g (γ s) = β (tL + s)) : gluedCurve β g γ tL = β := by
  funext s
  by_cases hs : s ≤ tL
  · exact gluedCurve_of_le hs
  · rw [gluedCurve, ite_eq_right_iff.2 (fun h => (hs h).elim), htail,
      add_tsub_cancel_of_le (le_of_not_ge hs)]

/-- A free original-real point beyond the old base supplies the right-side
anchor for the actual curve, even when the lifted tail contacts the old range. -/
theorem exists_right_anchor_of_actual_free_real
    {p : ℝ → ℂ} {β : ℝ≥0 → ℂ} {c : Chart} {g : ℂ → ℂ} {x : ℝ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hβ : IsProperCurve β) (hβ0 : β 0 = 0)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgi : EqOn g c.2.1 H) (hx : 0 < x) (hxR : realMax (p '' Icc 0 1) < x)
    (hxβ : (x : ℂ) ∉ range β) : ∃ w ∈ H, g w ∈ rightSide β := by
  have hxright := ofReal_mem_rightSide hβ hβ0 hx hxβ
  have hfree := isFreeAt_of_gt (isCompact_Icc.image_of_continuousOn hp)
    (fun y hy => (realBase_facts hp hp0).2.2.1 y hy |>.2) hxR
  have hDev : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H \ fillH (p '' Icc 0 1) :=
    eventually_mem_of_isFreeAt hfree
  have hRev : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ rightSide β :=
    Filter.eventually_mem_set.2
      (nhdsWithin_le_nhds ((isOpen_rightSide' hβ).mem_nhds hxright))
  have hne : (𝓝[H] (x : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_H_of_im_nonneg (by simp))
  obtain ⟨z, hzD, hzR⟩ := (hDev.and hRev).exists
  refine ⟨c.1 z, hc.1.fwd_mem hzD, ?_⟩
  rw [hgi (hc.1.fwd_mem hzD), hc.1.inv_fwd hzD]
  exact hzR

/-- Walks with nonpositive original-real contacts have the free right collar
needed in the reflected sewing chart, for every compact old base. -/
theorem exists_free_right_real_of_nonpos_contacts {β : ℝ≥0 → ℂ} (R : ℝ)
    (hreal : ∀ s, (β s).im = 0 → (β s).re ≤ 0) :
    ∃ x : ℝ, 0 < x ∧ R < x ∧ (x : ℂ) ∉ range β := by
  refine ⟨|R| + 1, by positivity, ?_, ?_⟩
  · linarith only [le_abs_self R]
  · rintro ⟨s, hs⟩
    have him : (β s).im = 0 := by rw [hs]; rfl
    have hre := hreal s him
    rw [hs, ofReal_re] at hre
    exact (not_le_of_gt (by positivity : (0 : ℝ) < |R| + 1)) hre

/-- The complete-tail specialization of S5 transports the entire relative
closed right side in the closed upper half-plane, including real contacts.
In SB4 this is used after reflection of the lower walk. -/
theorem image_closedRightSide_of_actual_tail
    {p : ℝ → ℂ} {β γ : ℝ≥0 → ℂ} {c : Chart} {g : ℂ → ℂ} {tL : ℝ≥0}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hβ : IsProperCurve β) (hβ0 : β 0 = 0)
    (hA : p '' Icc 0 1 ⊆ closedRightSide β)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hentry : β tL = realMin (p '' Icc 0 1))
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (htail : ∀ s, g (γ s) = β (tL + s))
    (hfree : ∃ x : ℝ, 0 < x ∧ realMax (p '' Icc 0 1) < x ∧ (x : ℂ) ∉ range β) :
    g '' (closedRightSide γ ∩ {z | 0 ≤ z.im}) ⊆ closedRightSide β := by
  have hβC : IsProperCompletion β tL β :=
    ⟨hβ.1, hβ.2.1, hβ.2.2.1, hβ.2.2.2, fun _ _ => rfl⟩
  have hglue := gluedCurve_eq_of_actual_tail htail
  have hΓ : IsProperCurve (gluedCurve β g γ tL) := by rw [hglue]; exact hβ
  have hΓ0 : gluedCurve β g γ tL 0 = 0 := by rw [hglue, hβ0]
  have hhead := s5_head_subset_hullK hp hp0 hpH hβ0 hβC hA le_rfl hentry
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
    hγ hγ0 hβ hβ0 (fun s _ => Or.inl ⟨tL + s, (htail s).symm⟩) hoff hleft hanchor
  apply s5_image_right_upper_of_interior hγ hγ0 hβ hβ0 hgc
  · intro t
    rw [htail]
    exact Or.inr (Or.inl (mem_range_self _))
  · intro w hw
    exact Or.inl (hright ⟨w, hw, rfl⟩)

/-- The previous physical history is retained in the sewn union; no buried
point is removed when adjoining an arbitrary subset of the transported side. -/
theorem union_subset_closedRightSide_of_actual_tail
    {p : ℝ → ℂ} {β γ : ℝ≥0 → ℂ} {c : Chart} {g : ℂ → ℂ} {tL : ℝ≥0}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hβ : IsProperCurve β) (hβ0 : β 0 = 0)
    (hA : p '' Icc 0 1 ⊆ closedRightSide β)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hentry : β tL = realMin (p '' Icc 0 1))
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (htail : ∀ s, g (γ s) = β (tL + s))
    (hfree : ∃ x : ℝ, 0 < x ∧ realMax (p '' Icc 0 1) < x ∧ (x : ℂ) ∉ range β)
    {C : Set ℂ} (hC : C ⊆ closedRightSide γ ∩ {z | 0 ≤ z.im}) :
    p '' Icc 0 1 ∪ g '' C ⊆ closedRightSide β :=
  union_subset hA ((image_mono hC).trans
    (image_closedRightSide_of_actual_tail hp hp0 hpH hβ hβ0 hA hc hgc hgi
      hentry hγ hγ0 htail hfree))

end InteractingSLE.Theorem14.SB
