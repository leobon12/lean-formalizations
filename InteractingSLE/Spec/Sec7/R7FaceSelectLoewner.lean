/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7FaceSelectChange

/-!
# Both finite mixed relative drivers with two remaining planar inputs

PROVE-R7-GAPEQ. The source certified-frontier data, contained attachment and the named
witness/bulge inputs imply the physical gap, erasure and relative Loewner evolution. The
global side inclusions, outer attachment, boundary avoidance and target access are proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.R7FaceSelect

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7GapEqCorner R7GateBridge

/-- **Finite left-outer relative evolution.** The only additional geometric inputs are the
two exact named propositions `GateWitnesses` and `GateBulges`. The contained attachment
hypothesis keeps its existing type; no germ comparison is strengthened here. -/
theorem relLoewner_leftOuter_of_witnesses {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ} {ψ : ℂ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H)
    (hψ : IsJordanCoord (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) ψ)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M))
    (hrevR : IsWallReverseVisit R η) (hvisR : IsWallVisited R η)
    (hrevM : IsWallReverseVisit M η) (hvisM : IsWallVisited M η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcR R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (hwitness : GateWitnesses W η (cfArcR R L r) (cfArcL R L r) (cfPocket R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (hbulges : GateBulges W η (cfArcR R L r) (cfArcL R L r)
      (cfPocket R L r) (negInv '' leftSideOf (range M))
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    RelLoewner
      (fun v => ψ (erasedPath η (cfPocket R L r)
        (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) v))
      (pocketClock η (cfPocket R L r)
        (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))
        (firstHit η (cfArcR R L r 0))) := by
  obtain ⟨hτ0, hτ, hσ, hxf⟩ := corner_firstHits_of_wall_visits h h0 hη.1 hη.2.1 (Or.inl hvisR)
  exact relLoewner_leftOuter_of_faces h h0 hM hO hcR hcL houter hη hW hW0 hηH hψ havoid
    hrevR hvisR hrevM hvisM h42 hAC (changePocket_subset_right_of_order h hO)
    (left_exterior_subset hO)
    (gate_faces_leftOuter h h0 hO hη hW hW0 hτ0 hτ hσ hxf hrevR
      (fun t ht => notMem_image_negInv (havoid t ht)) hwitness hbulges)

/-- **Finite right-outer relative evolution.** This includes the previously missing reflected
driver composition. The physical gap and the outer right attachment are conclusions. -/
theorem relLoewner_rightOuter_of_witnesses {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ} {ψ : ℂ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H)
    (hψ : IsJordanCoord (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) ψ)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M))
    (hrevL : IsWallReverseVisit L η) (hvisL : IsWallVisited L η)
    (hrevM : IsWallReverseVisit M η) (hvisM : IsWallVisited M η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcL R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (hwitness : GateWitnesses W η (cfArcL R L r) (cfArcR R L r) (cfPocket R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (hbulges : GateBulges W η (cfArcL R L r) (cfArcR R L r)
      (cfPocket R L r) (negInv '' rightSideOf (range M))
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    RelLoewner
      (fun v => ψ (erasedPath η (cfPocket R L r)
        (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) v))
      (pocketClock η (cfPocket R L r)
        (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))
        (firstHit η (cfArcR R L r 0))) := by
  have hC := h.isCfPocket h0
  have havoidB := fun t ht => notMem_image_negInv (havoid t ht)
  have hgap := pocketGapEq_rightOuter_of_witnesses h h0 hO hη hW hW0 hηH hrevL hvisL
    h42 hAC havoid hwitness hbulges
  have hP := isErasurePocket_rightOuter h (h.rightLo_pos h0) hM hO hcR hcL houter hη hW hW0
    havoid hrevL hrevM hvisM h42 hAC hgap
  have h42' := no_interval_frontier hC hη.2.1 h42
  have hcollar : ∀ v ∈ Ioo (0 : ℝ) 1,
      R7GapEq.HasExteriorCollar (cfPocket R L r) (negInv '' rightSideOf (range M))
        (frontier (cfPocket R L r)) (cfArcR R L r v) :=
    fun _ hv => R7GapEqGeo.hasExteriorCollar_cfArcR h h0
      (changePocket_subset_left_of_order h hO) (right_exterior_subset hO) Subset.rfl hv
  have hAC₁ := barrierAttachConst_of_outerCollars hη.2.1 hC.cont₁ hP.nonneg
    hP.first_y hP.fresh_x h42' havoidB hcollar
  have hfaces := gate_faces_rightOuter h h0 hO hη hW hW0 hP.nonneg hP.first_y hP.first_x
    hP.fresh_x hrevL havoidB hwitness hbulges
  apply relLoewner_of_change_gate_faces h h0 hP hη hW hW0 hηH hψ (Or.inr hrevL)
    hAC₁ hAC havoidB
  intro s hs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂
  have hf := hfaces s hs hsσ q₂ q₁ a₂ a₁ ha₂ ha₁
  rwa [union_comm (a₂ '' Icc 0 1) (a₁ '' Icc 0 1), min_comm q₂ q₁, max_comm q₂ q₁] at hf

end InteractingSLE.Sec7.R7FaceSelect
