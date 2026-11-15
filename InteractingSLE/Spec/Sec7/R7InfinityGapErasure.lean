/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapLeft
import InteractingSLE.Spec.Sec7.R7InfinityGapRight

/-!
# Infinite mixed erasure from the contained attachment comparison

PROVE-R7-GAPEQ. The proved physical gap equality discharges the gap premise of
the landed erasure assemblies. The first entrance and its freshness follow from
the contained wall's visitation; no old-access or face hypothesis remains.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.R7InfinityGap

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn

/-- Actual infinite left-outer erasure with the contained comparison explicit.
The former physical gap equality input is proved. -/
theorem isErasurePocketInf_leftOuter_of_containedAttach {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevR : IsWallReverseVisit R η) (hvisR : IsWallVisited R η)
    (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M))
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConstInf η (cfPocket R L r) (cfArcRInf R L r)
      (firstHit η (cfArcRInf R L r 0))) :
    IsErasurePocketInf η (cfPocket R L r) (cfArcRInf R L r 0)
      (firstHit η (cfArcRInf R L r 0)) := by
  obtain ⟨-, hhi, hlt, -⟩ := h.changeCorner_props
  have hvis : ∃ t, cfArcRInf R L r 0 ∈ η '' Icc 0 t := by
    simpa only [cfArcRInf, add_zero, div_one] using
      wall_visited hη.1 h.right hvisR ⟨h0 ▸ hlt, hhi.2⟩
  obtain ⟨hτ0, hτ, hτf⟩ := firstHit_spec hη.2.1 hvis
  have hgap := pocketGapEqInf_leftOuter h h0 hM hO hcR hcL houter hη hW hW0
    hτ0 hτ hrevR hrevM havoid h42 hAC (by rw [hτ]; exact hτf)
  exact R7StopIn.isErasurePocketInf_leftOuter h h0 hM hO hcR hcL houter hη havoid
    hrevR hvisR hrevM hAC hgap

/-- Actual infinite right-outer erasure with the contained comparison explicit.
The common entrance is obtained by visiting the contained left wall. -/
theorem isErasurePocketInf_rightOuter_of_containedAttach {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevL : IsWallReverseVisit L η) (hvisL : IsWallVisited L η)
    (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M))
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConstInf η (cfPocket R L r) (cfArcLInf R L r)
      (firstHit η (cfArcRInf R L r 0))) :
    IsErasurePocketInf η (cfPocket R L r) (cfArcRInf R L r 0)
      (firstHit η (cfArcRInf R L r 0)) := by
  have hC := h.isCfPocketInf h0
  obtain ⟨-, -, -, -, hhi, hlt, -⟩ := h.changeCorner_props
  have hvis : ∃ t, cfArcLInf R L r 0 ∈ η '' Icc 0 t := by
    simpa only [cfArcLInf, add_zero, div_one] using
      wall_visited hη.1 h.left hvisL ⟨h.leftLo_eq_zero_of_rightLo_eq_zero h0 ▸ hlt, hhi.2⟩
  obtain ⟨hτ0, hτ, hτf⟩ := firstHit_spec hη.2.1 (hC.seed ▸ hvis)
  have hgap := pocketGapEqInf_rightOuter h h0 hM hO hcR hcL houter hη hW hW0
    hτ0 hτ hrevL hrevM havoid h42 hAC (by rw [hτ]; exact hτf)
  exact R7StopIn.isErasurePocketInf_rightOuter h h0 hM hO hcR hcL houter hη havoid
    hrevL hvisL hrevM hAC hgap

end InteractingSLE.Sec7.R7InfinityGap
