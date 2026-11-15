/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityAccessSelection

/-!
# Actual mixed infinite-end component charts

PROVE-R7-GAPEQ. Both orientations now have a compactified Jordan component chart
with no chart, side-selection, exterior-access or pocket-witness hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7InfinityAccess

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn

/-- A genuine left-outer infinite pocket has the previously named component
chart. Only its contained right arm is required to be reverse visited. -/
theorem exists_infiniteFaceChart_leftOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevR : IsWallReverseVisit R η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M)) :
    ∀ s, τ ≤ s → ∃ (a : ℝ) (Γ : Set ℂ) (q : ℂ),
      R7EndFace.InfiniteFaceChart W (cfPocket R L r) s a Γ q := by
  intro s hτs
  obtain ⟨hE, hEH, hEb, hEC, houter⟩ := left_outer_exterior_props h h0 hO
  obtain ⟨-, hhi, hlt, -⟩ := h.changeCorner_props
  have hb : 0 < rightHi R L r := h0 ▸ hlt
  refine exists_infiniteFaceChart_of_exterior (h.isCfPocketInf h0) hη hW hW0 hτ0 hτs hτ
    (rev_inf_of_wall h.right hη.1 hrevR hb hhi.2) hE hEH hEb ?_ hEC houter
    (Or.inl fun x hx => positive_real_mem_closure_left_exterior h.left hx) ?_
  · refine Set.disjoint_left.2 ?_
    rintro _ hz ⟨t, ht, rfl⟩
    exact notMem_image_negInv (havoid t ht.1) (R7FaceSelect.left_exterior_subset hO hz)
  · intro z hz hzH
    exact OuterIn.isLocConnWithin_compl_closure_cfPocket h hzH
      (neg_cayley_mem_frontier h.isOpen_changePocket h.changePocket_subset_H hz)

/-- The reflected right-outer pocket has the same chart, keeping the original
right-labeled entrance while only the contained left arm is reverse visited. -/
theorem exists_infiniteFaceChart_rightOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevL : IsWallReverseVisit L η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M)) :
    ∀ s, τ ≤ s → ∃ (a : ℝ) (Γ : Set ℂ) (q : ℂ),
      R7EndFace.InfiniteFaceChart W (cfPocket R L r) s a Γ q := by
  intro s hτs
  have hC := h.isCfPocketInf h0
  obtain ⟨hE, hEH, hEb, hEC, houter⟩ := right_outer_exterior_props h h0 hO
  obtain ⟨-, -, -, -, hhi, hlt, -⟩ := h.changeCorner_props
  have hb : 0 < leftHi R L r := h.leftLo_eq_zero_of_rightLo_eq_zero h0 ▸ hlt
  refine exists_infiniteFaceChart_of_exterior (cfPocketInf_swap hC) hη hW hW0 hτ0 hτs
    (hτ.trans hC.seed.symm) (rev_inf_of_wall h.left hη.1 hrevL hb hhi.2)
    hE hEH hEb ?_ hEC houter
    (Or.inr fun x hx => negative_real_mem_closure_right_exterior h.right hx) ?_
  · refine Set.disjoint_left.2 ?_
    rintro _ hz ⟨t, ht, rfl⟩
    exact notMem_image_negInv (havoid t ht.1) (R7FaceSelect.right_exterior_subset hO hz)
  · intro z hz hzH
    exact OuterIn.isLocConnWithin_compl_closure_cfPocket h hzH
      (neg_cayley_mem_frontier h.isOpen_changePocket h.changePocket_subset_H hz)

end InteractingSLE.Sec7.R7InfinityAccess
