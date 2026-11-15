/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7RelativeInfClock

/-!
# Actual infinite component charts with an arbitrarily negative pole

PROVE-R7-GAPEQ. Strengthen the landed chart existence adapter to choose its
real pole below any prescribed bound. This permits compactifying an entire
collapsed own-future without a separate pole-avoidance hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7RelativeInf

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7InfinityChart R7InfinityAccess

/-- Exterior side selection gives a component chart with pole below any bound. -/
theorem exists_chart_below_of_exterior {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C E : Set ℂ} {τ s : ℝ} (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτs : τ ≤ s) (hτ : η τ = A₁ 0)
    (hrev : IsReverseVisitOrderInf A₁ fun t => η '' Icc 0 t)
    (hE : IsPreconnected E) (hEH : E ⊆ H) (hEb : ¬ IsBounded E)
    (havoid : Disjoint E (η '' Icc 0 s)) (hEC : E ⊆ (closure C)ᶜ)
    (houter : A₂ '' Ici 0 ⊆ closure E)
    (hreal : (∀ x : ℝ, 0 < x → (x : ℂ) ∈ closure E) ∨
      (∀ x : ℝ, x < 0 → (x : ℂ) ∈ closure E))
    (hloc : ∀ z ∈ frontier C, z ∈ H → IsLocConnWithin (closure C)ᶜ z) (B : ℝ) :
    ∃ a < B, ∃ (Γ : Set ℂ) (q : ℂ), R7EndFace.InfiniteFaceChart W C s a Γ q := by
  obtain ⟨q₁, q₂, hq⟩ := exists_pocket_chart_reduction hC hη hW hW0 hτ0 hτs hτ
  let a := min (min q₁ q₂) B - 1
  have ha : a < min q₁ q₂ := (sub_one_lt _).trans_le (min_le_left _ _)
  obtain ⟨b₁, b₂, hb₁, hb₂, hΓ, hΓH, -, -, hchart⟩ := hq _ ha
  have hsides := infiniteFaceSides_of_exterior hC hη hW hW0 hτ0 hτs hτ hrev hb₁ hb₂ ha
    hΓ hΓH hE hEH hEb havoid hEC houter hreal hloc
  obtain ⟨q, hq⟩ := hchart hsides
  exact ⟨a, (sub_one_lt _).trans_le (min_le_right _ _), _, q, hq⟩

/-- A genuine left-outer infinite pocket has the previously named component
chart. Only its contained right arm is required to be reverse visited. -/
theorem exists_chart_below_leftOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevR : IsWallReverseVisit R η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M)) :
    ∀ s, τ ≤ s → ∀ B : ℝ, ∃ a < B, ∃ (Γ : Set ℂ) (q : ℂ),
      R7EndFace.InfiniteFaceChart W (cfPocket R L r) s a Γ q := by
  intro s hτs B
  obtain ⟨hE, hEH, hEb, hEC, houter⟩ := left_outer_exterior_props h h0 hO
  obtain ⟨-, hhi, hlt, -⟩ := h.changeCorner_props
  have hb : 0 < rightHi R L r := h0 ▸ hlt
  refine exists_chart_below_of_exterior (h.isCfPocketInf h0) hη hW hW0 hτ0 hτs hτ
    (rev_inf_of_wall h.right hη.1 hrevR hb hhi.2) hE hEH hEb ?_ hEC houter
    (Or.inl fun x hx => positive_real_mem_closure_left_exterior h.left hx) ?_ B
  · refine Set.disjoint_left.2 ?_
    rintro _ hz ⟨t, ht, rfl⟩
    exact notMem_image_negInv (havoid t ht.1) (R7FaceSelect.left_exterior_subset hO hz)
  · intro z hz hzH
    exact OuterIn.isLocConnWithin_compl_closure_cfPocket h hzH
      (neg_cayley_mem_frontier h.isOpen_changePocket h.changePocket_subset_H hz)

/-- The reflected right-outer pocket has the same chart, keeping the original
right-labeled entrance while only the contained left arm is reverse visited. -/
theorem exists_chart_below_rightOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevL : IsWallReverseVisit L η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M)) :
    ∀ s, τ ≤ s → ∀ B : ℝ, ∃ a < B, ∃ (Γ : Set ℂ) (q : ℂ),
      R7EndFace.InfiniteFaceChart W (cfPocket R L r) s a Γ q := by
  intro s hτs B
  have hC := h.isCfPocketInf h0
  obtain ⟨hE, hEH, hEb, hEC, houter⟩ := right_outer_exterior_props h h0 hO
  obtain ⟨-, -, -, -, hhi, hlt, -⟩ := h.changeCorner_props
  have hb : 0 < leftHi R L r := h.leftLo_eq_zero_of_rightLo_eq_zero h0 ▸ hlt
  refine exists_chart_below_of_exterior (cfPocketInf_swap hC) hη hW hW0 hτ0 hτs
    (hτ.trans hC.seed.symm) (rev_inf_of_wall h.left hη.1 hrevL hb hhi.2)
    hE hEH hEb ?_ hEC houter
    (Or.inr fun x hx => negative_real_mem_closure_right_exterior h.right hx) ?_ B
  · refine Set.disjoint_left.2 ?_
    rintro _ hz ⟨t, ht, rfl⟩
    exact notMem_image_negInv (havoid t ht.1) (R7FaceSelect.right_exterior_subset hO hz)
  · intro z hz hzH
    exact OuterIn.isLocConnWithin_compl_closure_cfPocket h hzH
      (neg_cayley_mem_frontier h.isOpen_changePocket h.changePocket_subset_H hz)

end InteractingSLE.Sec7.R7RelativeInf
