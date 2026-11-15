/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7SurviveBarriers
import InteractingSLE.Spec.Sec7.R7SurviveClipping

/-!
# Physical target adherence for the actual finite mixed pockets

PROVE-R7-GAPEQ. The contained wall and clipped certified frontier give both reverse
barriers. Thus the formerly named planar adherence hypothesis is discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull)
open scoped NNReal

namespace InteractingSLE.Sec7.R7Survive

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7GapEqCorner R7LocalFace

/-- Every allowed surviving component of a finite left-outer pocket adheres to its
fresh target. No gate-selection or component-adherence premise remains. -/
theorem allowedTargetAdherence_leftOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ σ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcR R L r 1) (hσ : η σ = cfArcR R L r 0)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ)
    (hrevR : IsWallReverseVisit R η) (hrevM : IsWallReverseVisit M η) :
    AllowedTargetAdherence W (cfPocket R L r) (negInv '' leftSideOf (range M))
      (cfArcR R L r 0) τ σ := by
  have hC := h.isCfPocket h0
  obtain ⟨B, hBc, hBH, hBcl, hBrev, hB0, hB1, hBmem⟩ :=
    exists_closed_midBarrier h h0 hM hO hcR hcL hη.1 hrevM
  obtain ⟨hFo, hFfr⟩ := forbidden_left hM
  have hfr : frontier (cfPocket R L r) ⊆
      negInv '' leftSideOf (range M) ∪ (cfArcR R L r '' Icc 0 1 ∪ B '' Icc 0 1) := by
    rw [hC.frontier_eq]
    rintro z (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
    · rcases cfArcL_mem_of_outer h (h.rightLo_pos h0) houter hB1 hBmem hv with hF | hB
      exacts [Or.inl hF, Or.inr (Or.inr hB)]
  intro s hτs hsσ
  obtain ⟨hu0, -, hD, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₁ hC.mem_H₁
    hτ0 hτs hsσ hτ hσ hxf
  apply target_adherence_of_barriers hη hW hW0 (hτ0.trans hτs) hC.isOpen hC.isBounded
    (fun p hp => isLocConnWithin_pocket hC.isOpen hC.isConnected hC.isBounded
      (R7GapEqFin.isJordanCurve_frontier_of_isCfPocket hC) hp)
    hFo hC.cont₁ hBc hC.mem_H₁ hBH
    (fun z hz => frontier_subset_closure (by rw [hC.frontier_eq]; exact Or.inl hz)) hBcl
    (cfArcR_rev h h0 hη.1 hrevR) hBrev hB0 (hD 0 ⟨le_rfl, hu0⟩)
    ⟨τ, ⟨hτ0, hτs⟩, hτ⟩ ⟨τ, ⟨hτ0, hτs⟩, hτ.trans hB1.symm⟩ hfr
  exact fun z hz => Or.inr (hBmem z hz.1.1 hz.2 (hFfr z hz.1.2 hz.2))

/-- The reflected finite right-outer pocket, retaining the original right-labeled
entrance and target times. -/
theorem allowedTargetAdherence_rightOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ σ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcR R L r 1) (hσ : η σ = cfArcR R L r 0)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ)
    (hrevL : IsWallReverseVisit L η) (hrevM : IsWallReverseVisit M η) :
    AllowedTargetAdherence W (cfPocket R L r) (negInv '' rightSideOf (range M))
      (cfArcR R L r 0) τ σ := by
  have hC := h.isCfPocket h0
  obtain ⟨B, hBc, hBH, hBcl, hBrev, hB0, hB1, hBmem⟩ :=
    exists_closed_midBarrier h h0 hM hO hcR hcL hη.1 hrevM
  obtain ⟨hFo, hFfr⟩ := forbidden_right hM
  have hfr : frontier (cfPocket R L r) ⊆
      negInv '' rightSideOf (range M) ∪ (cfArcL R L r '' Icc 0 1 ∪ B '' Icc 0 1) := by
    rw [hC.frontier_eq]
    rintro z (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · rcases cfArcR_mem_of_outer h (h.rightLo_pos h0) houter hB1 hBmem hv with hF | hB
      exacts [Or.inl hF, Or.inr (Or.inr hB)]
    · exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
  intro s hτs hsσ
  obtain ⟨hu0, -, hD, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₁ hC.mem_H₁
    hτ0 hτs hsσ hτ hσ hxf
  rw [← hC.junction]
  apply target_adherence_of_barriers hη hW hW0 (hτ0.trans hτs) hC.isOpen hC.isBounded
    (fun p hp => isLocConnWithin_pocket hC.isOpen hC.isConnected hC.isBounded
      (R7GapEqFin.isJordanCurve_frontier_of_isCfPocket hC) hp)
    hFo hC.cont₂ hBc hC.mem_H₂ hBH
    (fun z hz => frontier_subset_closure (by rw [hC.frontier_eq]; exact Or.inr hz)) hBcl
    (cfArcL_rev h h0 hη.1 hrevL) hBrev (hB0.trans hC.junction.symm)
    (hC.junction ▸ hD 0 ⟨le_rfl, hu0⟩)
    ⟨τ, ⟨hτ0, hτs⟩, hτ.trans hC.seed.symm⟩ ⟨τ, ⟨hτ0, hτs⟩, hτ.trans hB1.symm⟩ hfr
  exact fun z hz => Or.inr (hBmem z hz.1.1 hz.2 (hFfr z hz.1.2 hz.2))

end InteractingSLE.Sec7.R7Survive
