/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapCurrent

/-!
# Actual selected faces for every admissible compactifying pole

PROVE-R7-GAPEQ. The proved exterior side selection supplies the face hypotheses
of the gap theorem for any current arms and any pole left of their gates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7InfinityGap

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7InfinityChart R7InfinityAccess

/-- Every admissible compact face of the actual left-outer pocket has physical
image in the pocket and confines active future visits. -/
theorem current_faces_leftOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevR : IsWallReverseVisit R η) (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M)) :
    ∀ s, τ ≤ s → ∀ (p q₁ q₂ : ℝ) (b₁ b₂ : ℝ → ℂ),
      IsLastVisitArm W η (cfArcRInf R L r) s p q₁ b₁ →
      IsLastVisitArm W η (cfArcLInf R L r) s p q₂ b₂ → p < min q₁ q₂ →
      LQGMetric.JordanMap.IsJordanCurve (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)) →
      compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹) ⊆ Hbar →
      MapsTo (fun ζ => trMap W 0 s (psiMapInv p ζ))
        (innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹))) (cfPocket R L r) ∧
      ∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
        psiMap p (trMap W s t 0) ∈ innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)) := by
  intro s hτs p q₁ q₂ b₁ b₂ hb₁ hb₂ hp hΓ hΓH
  have hC := h.isCfPocketInf h0
  have hs := hτ0.trans hτs
  obtain ⟨hE, hEH, hEb, hEC, houterE⟩ := left_outer_exterior_props h h0 hO
  obtain ⟨-, hhi, hlt, -⟩ := h.changeCorner_props
  have hhi0 : 0 < rightHi R L r := h0 ▸ hlt
  have hrev := rev_inf_of_wall h.right hη.1 hrevR hhi0 hhi.2
  have hsides := infiniteFaceSides_of_exterior hC hη hW hW0 hτ0 hτs hτ hrev hb₁ hb₂ hp hΓ hΓH
    hE hEH hEb (Set.disjoint_left.2 (by
      rintro _ hz ⟨t, ht, rfl⟩
      exact notMem_image_negInv (havoid t ht.1) (R7FaceSelect.left_exterior_subset hO hz)))
    hEC houterE (Or.inl fun x hx => positive_real_mem_closure_left_exterior h.left hx)
    (fun z hz hzH => OuterIn.isLocConnWithin_compl_closure_cfPocket h hzH
      (neg_cayley_mem_frontier h.isOpen_changePocket h.changePocket_subset_H hz))
  have hbd := compactBoundary_mem_frontier hC hη hW hW0 hτ0 hτs hτ hb₁ hb₂
  obtain ⟨q, hchart⟩ := infiniteFaceChart_of_sides hη hW hW0 hs hC.isOpen hΓ hΓH
    (zero_mem_compactBoundary (b₂ := b₂) hb₁.2.2.2.1)
    (fun ζ hζ hζH hzC => (hC.isOpen.frontier_eq ▸ hbd ζ hζ hζH).2 hzC) hsides
  have hallowed := R7EndFace.allowedUnboundedComponents_leftOuter h h0 hM hO hcR hcL
    houter hη hW hW0 hτ0 hτ hrevR hrevM
  refine ⟨?_, R7EndFace.ownFuture_mem_infinite_face h h0 hη hW hW0 hs hτs hallowed hchart
    (fun t ht => notMem_image_negInv (havoid t (hs.trans ht)))⟩
  apply mapsTo_iff_image_subset.2
  rw [hchart.2.2.2.2.2]
  exact (connectedComponentIn_subset _ _).trans inter_subset_left

/-- The reflected actual right-outer pocket has the same arbitrary-pole face
properties, with its contained left arm first. -/
theorem current_faces_rightOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevL : IsWallReverseVisit L η) (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M)) :
    ∀ s, τ ≤ s → ∀ (p q₁ q₂ : ℝ) (b₁ b₂ : ℝ → ℂ),
      IsLastVisitArm W η (cfArcLInf R L r) s p q₁ b₁ →
      IsLastVisitArm W η (cfArcRInf R L r) s p q₂ b₂ → p < min q₁ q₂ →
      LQGMetric.JordanMap.IsJordanCurve (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)) →
      compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹) ⊆ Hbar →
      MapsTo (fun ζ => trMap W 0 s (psiMapInv p ζ))
        (innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹))) (cfPocket R L r) ∧
      ∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
        psiMap p (trMap W s t 0) ∈ innerSide (compactBoundary b₁ b₂ (-(q₁-p)⁻¹) (-(q₂-p)⁻¹)) := by
  intro s hτs p q₁ q₂ b₁ b₂ hb₁ hb₂ hp hΓ hΓH
  have hC₀ := h.isCfPocketInf h0
  have hC := cfPocketInf_swap hC₀
  have hτ' := hτ.trans hC₀.seed.symm
  have hs := hτ0.trans hτs
  obtain ⟨hE, hEH, hEb, hEC, houterE⟩ := right_outer_exterior_props h h0 hO
  obtain ⟨-, -, -, -, hhi, hlt, -⟩ := h.changeCorner_props
  have hhi0 : 0 < leftHi R L r := h.leftLo_eq_zero_of_rightLo_eq_zero h0 ▸ hlt
  have hrev := rev_inf_of_wall h.left hη.1 hrevL hhi0 hhi.2
  have hsides := infiniteFaceSides_of_exterior hC hη hW hW0 hτ0 hτs hτ' hrev hb₁ hb₂ hp hΓ hΓH
    hE hEH hEb (Set.disjoint_left.2 (by
      rintro _ hz ⟨t, ht, rfl⟩
      exact notMem_image_negInv (havoid t ht.1) (R7FaceSelect.right_exterior_subset hO hz)))
    hEC houterE (Or.inr fun x hx => negative_real_mem_closure_right_exterior h.right hx)
    (fun z hz hzH => OuterIn.isLocConnWithin_compl_closure_cfPocket h hzH
      (neg_cayley_mem_frontier h.isOpen_changePocket h.changePocket_subset_H hz))
  have hbd := compactBoundary_mem_frontier hC hη hW hW0 hτ0 hτs hτ' hb₁ hb₂
  obtain ⟨q, hchart⟩ := infiniteFaceChart_of_sides hη hW hW0 hs hC.isOpen hΓ hΓH
    (zero_mem_compactBoundary (b₂ := b₂) hb₁.2.2.2.1)
    (fun ζ hζ hζH hzC => (hC.isOpen.frontier_eq ▸ hbd ζ hζ hζH).2 hzC) hsides
  have hallowed := R7EndFace.allowedUnboundedComponents_rightOuter h h0 hM hO hcR hcL
    houter hη hW hW0 hτ0 hτ hrevL hrevM
  refine ⟨?_, R7EndFace.ownFuture_mem_infinite_face h h0 hη hW hW0 hs hτs hallowed hchart
    (fun t ht => notMem_image_negInv (havoid t (hs.trans ht)))⟩
  apply mapsTo_iff_image_subset.2
  rw [hchart.2.2.2.2.2]
  exact (connectedComponentIn_subset _ _).trans inter_subset_left

end InteractingSLE.Sec7.R7InfinityGap
