/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetApproach
import InteractingSLE.Spec.Supplement.SBLemmaS2
import InteractingSLE.Spec.Sec7.Lemma77Sep

/-!
# The opposite-hull exclusion for G8 in the nonhitting left sector

Packet PROVE-G8-DET. The source chooses the first curve's left weights in the
nonhitting sector. The resulting absence of negative real contacts makes every
point on its closed left side, off a finite prefix, exterior to that prefix's
filled hull. We specialize the existing left-component lemma of S2 and the
free/trapped propagation lemmas; no new planar separation theorem is needed.

The nonnegative-real-prefix hypothesis below is explicit. It is not present in
`RLC.G8DetFrameStatement`, and this file does not claim to prove that statement.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.RLC.G8Det

open Supp9B HalfPlaneSep

/-- If a compact part `F` of a proper curve has no negative real points, its
open left side in `ℍ` is outside the filling of `F`. The component is either
unbounded or adherent to a negative real gap, which is free for `F`. -/
theorem isFreeAt_of_mem_leftSide_of_nonneg_real {γ : ℝ≥0 → ℂ}
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {F : Set ℂ} (hF : IsCompact F)
    (hFγ : F ⊆ range γ) (hreal : ∀ z ∈ F, z.im = 0 → 0 ≤ z.re)
    {z : ℂ} (hz : z ∈ leftSide γ ∩ H) : IsFreeAt F z := by
  set C := connectedComponentIn (leftSide γ ∩ H) z with hC
  have hzC : z ∈ C := mem_connectedComponentIn hz
  have hCsub : C ⊆ {w : ℂ | 0 ≤ w.im} \ F := by
    intro w hw
    have hw' := connectedComponentIn_subset (leftSide γ ∩ H) z hw
    exact ⟨show 0 ≤ w.im from le_of_lt hw'.2, fun hwF =>
      Theorem14.SB.notMem_range_of_mem_leftSide hw'.1 (hFγ hwF)⟩
  rcases Theorem14.SB.unbounded_or_gap hγ hγ0 hz with hu | ⟨x, hx, hxγ, hxC⟩
  · exact isFreeAt_of_not_isBounded hF.isClosed hF.isBounded
      isPreconnected_connectedComponentIn hu hCsub z hzC
  · have hxF : (x : ℂ) ∉ F := fun h => hxγ (hFγ h)
    have hxfree : IsFreeAt F (x : ℂ) := Theorem14.SB.isFreeAt_of_lt hF
      (fun y hy => by simpa only [ofReal_re] using hreal y hy (ofReal_im y)) hx
    have hpc : IsPreconnected (insert (x : ℂ) C) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
        (insert_subset hxC subset_closure)
    have hXF : insert (x : ℂ) C ⊆ {w : ℂ | 0 ≤ w.im} \ F := by
      rintro w (rfl | hw)
      · exact ⟨show 0 ≤ (x : ℂ).im by simp only [ofReal_im, le_refl], hxF⟩
      · exact hCsub hw
    exact Theorem14.SB.isFreeAt_of_isPreconnected hF.isClosed hpc
      hXF (mem_insert _ _) hxfree (mem_insert_of_mem _ hzC)

/-- The closed-side version, including a point on a later part of the curve.
The explicit nonnegative-real hypothesis is the source's left nonhitting input. -/
theorem mem_H_diff_fillH_of_closedLeftSide_of_nonneg_real {γ : ℝ≥0 → ℂ}
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {F : Set ℂ} (hF : IsCompact F)
    (hFγ : F ⊆ range γ) (hreal : ∀ z ∈ F, z.im = 0 → 0 ≤ z.re)
    {z : ℂ} (hz : z ∈ closedLeftSide γ) (hzH : z ∈ H) (hzF : z ∉ F) :
    z ∈ H \ fillH F := by
  have hleft : leftSide γ ∩ H ⊆ H \ fillH F := fun w hw =>
    Supp9D.mem_of_isFreeAt (isFreeAt_of_mem_leftSide_of_nonneg_real hγ hγ0 hF hFγ hreal hw) hw.2
  have hzcl : z ∈ closure (leftSide γ) := by
    rcases hz with hz | hz
    · exact subset_closure hz
    · exact seedRayClosure_subset_closure_leftSide hγ (by rw [hγ0]; rfl) hz
  have hzclH : z ∈ closure (leftSide γ ∩ H) := by
    rw [inter_comm]
    exact QuantumZipper.isOpen_H.inter_closure ⟨hzH, hzcl⟩
  exact Sec7.mem_H_diff_fillH_of_isFreeAt
    (Sec7.isFreeAt_of_mem_closure hF.isClosed hzF (closure_mono hleft hzclH)) hzH

/-- The missing opposite-hull exclusion follows from nonnegative real contacts
of the first prefix. This is a conditional local helper, not G8's declaration. -/
theorem second_tip_outside_of_nonneg_real {α β : ℝ≥0 → ℂ}
    (hcop : Sec7.Prop74Order.IsCompleteOrderedPair α β) (hα0 : α 0 = 0)
    {σ r : ℝ≥0} (hreal : ∀ t ≤ σ, (α t).im = 0 → 0 ≤ (α t).re)
    (hβH : β r ∈ H) (hβoff : β r ∉ α '' Icc 0 σ) :
    β r ∈ H \ fillH (α '' Icc 0 σ) := by
  obtain ⟨hα, hiα, hHα, hpα, _, _, _, _, hord⟩ := hcop
  exact mem_H_diff_fillH_of_closedLeftSide_of_nonneg_real ⟨hα, hiα, hHα, hpα⟩ hα0
    (isCompact_Icc.image hα) (image_subset_range _ _) (by
      rintro _ ⟨t, ht, rfl⟩ him
      exact hreal t ht.2 him) (hord (mem_range_self r)) hβH hβoff

end InteractingSLE.RLC.G8Det
