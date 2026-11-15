/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapAssembly
import InteractingSLE.Spec.Sec7.OuterInCollarInf

/-!
# Source collar and reverse-visit inputs for infinite mixed gaps

PROVE-R7-GAPEQ. The actual outer collars and Aux. 42 discharge the auxiliary
boundary hypotheses. Only the contained arm needs reverse visits.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal

namespace InteractingSLE.Sec7.R7InfinityGap

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7GapEq

/-- Actual left-outer collars, boundary nondegeneracy and contained reverse visits. -/
theorem gap_data_leftOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hrevR : IsWallReverseVisit R η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) :
    IsReverseVisitOrderInf (cfArcRInf R L r) (fun t => η '' Icc 0 t) ∧
    (∀ a b : ℝ, 0 ≤ a → a < b → ¬ η '' Icc a b ⊆ frontier (cfPocket R L r)) ∧
    ∀ v ∈ Ioi (0 : ℝ), HasExteriorCollar (cfPocket R L r)
      (negInv '' leftSideOf (range M)) (frontier (cfPocket R L r)) (cfArcLInf R L r v) := by
  have hC := h.isCfPocketInf h0
  obtain ⟨-, hhi, hlt, -⟩ := h.changeCorner_props
  refine ⟨rev_inf_of_wall h.right hη.1 hrevR (h0 ▸ hlt) hhi.2, ?_, ?_⟩
  · rw [hC.frontier_eq]
    exact OuterIn.no_interval_frontier_inf hC.cont₁ hC.cont₂ hC.inj₁ hC.inj₂ hη.2.1 h42
  · intro v hv
    exact OuterIn.hasExteriorCollar_cfArcLInf h h0
      (R7FaceSelect.changePocket_subset_right_of_order h hO)
      (R7FaceSelect.left_exterior_subset hO) Subset.rfl hv

/-- Actual right-outer collars, boundary nondegeneracy and contained reverse visits. -/
theorem gap_data_rightOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hrevL : IsWallReverseVisit L η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) :
    IsReverseVisitOrderInf (cfArcLInf R L r) (fun t => η '' Icc 0 t) ∧
    (∀ a b : ℝ, 0 ≤ a → a < b → ¬ η '' Icc a b ⊆ frontier (cfPocket R L r)) ∧
    ∀ v ∈ Ioi (0 : ℝ), HasExteriorCollar (cfPocket R L r)
      (negInv '' rightSideOf (range M)) (frontier (cfPocket R L r)) (cfArcRInf R L r v) := by
  have hC := h.isCfPocketInf h0
  obtain ⟨-, -, -, -, hhi, hlt, -⟩ := h.changeCorner_props
  have hhi0 : 0 < leftHi R L r := h.leftLo_eq_zero_of_rightLo_eq_zero h0 ▸ hlt
  refine ⟨rev_inf_of_wall h.left hη.1 hrevL hhi0 hhi.2, ?_, ?_⟩
  · rw [hC.frontier_eq]
    exact OuterIn.no_interval_frontier_inf hC.cont₁ hC.cont₂ hC.inj₁ hC.inj₂ hη.2.1 h42
  · intro v hv
    exact OuterIn.hasExteriorCollar_cfArcRInf h h0
      (R7FaceSelect.changePocket_subset_left_of_order h hO)
      (R7FaceSelect.right_exterior_subset hO) Subset.rfl hv

end InteractingSLE.Sec7.R7InfinityGap
