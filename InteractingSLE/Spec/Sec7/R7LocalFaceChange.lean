/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LocalFaceActual

/-!
# Finite mixed physical gaps with a physical component-adherence input

PROVE-R7-GAPEQ. The actual face witnesses and boundary avoidance are proved. The remaining
planar input is `AllowedTargetAdherence`; contained attachment comparisons retain their
landed type. No source theorem or landed statement is changed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.R7LocalFace

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7GapEqCorner R7FaceSelect

/-- The finite left-outer physical gap from physical target adherence.
The former witness and bulge hypotheses are absent. -/
theorem pocketGapEq_leftOuter_of_target_adherence {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H) (hrev : IsWallReverseVisit R η) (hvis : IsWallVisited R η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcR R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M))
    (haccess : AllowedTargetAdherence W (cfPocket R L r) (negInv '' leftSideOf (range M))
      (cfArcR R L r 0) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    PocketGapEq η (cfPocket R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) := by
  obtain ⟨hτ0, hτ, hσ, hxf⟩ := corner_firstHits_of_wall_visits h h0 hη.1 hη.2.1 (Or.inl hvis)
  have havoidB := fun t ht => notMem_image_negInv (havoid t ht)
  have hfaces := gate_faces_leftOuter_of_target_adherence h h0 hO hη hW hW0
    hτ0 hτ hσ hxf hrev havoidB haccess
  exact R7GateBridge.pocketGapEq_leftOuter_of_faces h h0 hη hW hW0 hηH hrev hvis h42 hAC
    havoidB (changePocket_subset_right_of_order h hO) (left_exterior_subset hO) hfaces

/-- The finite right-outer physical gap from physical target adherence.
The former witness and bulge hypotheses are absent. -/
theorem pocketGapEq_rightOuter_of_target_adherence {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H) (hrev : IsWallReverseVisit L η) (hvis : IsWallVisited L η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcL R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M))
    (haccess : AllowedTargetAdherence W (cfPocket R L r) (negInv '' rightSideOf (range M))
      (cfArcR R L r 0) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    PocketGapEq η (cfPocket R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) := by
  obtain ⟨hτ0, hτ, hσ, hxf⟩ := corner_firstHits_of_wall_visits h h0 hη.1 hη.2.1 (Or.inr hvis)
  have havoidB := fun t ht => notMem_image_negInv (havoid t ht)
  have hfaces := gate_faces_rightOuter_of_target_adherence h h0 hO hη hW hW0
    hτ0 hτ hσ hxf hrev havoidB haccess
  exact R7GateBridge.pocketGapEq_rightOuter_of_faces h h0 hη hW hW0 hηH hrev hvis h42 hAC
    havoidB (changePocket_subset_left_of_order h hO) (right_exterior_subset hO) hfaces

end InteractingSLE.Sec7.R7LocalFace
