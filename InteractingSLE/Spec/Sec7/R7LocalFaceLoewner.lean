/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LocalFaceActual

/-!
# Finite mixed relative drivers with a physical component-adherence input

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

/-- The finite left-outer relative driver from physical target adherence.
The former witness and bulge hypotheses are absent. -/
theorem relLoewner_leftOuter_of_target_adherence {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
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
    (haccess : AllowedTargetAdherence W (cfPocket R L r) (negInv '' leftSideOf (range M))
      (cfArcR R L r 0) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    RelLoewner
      (fun v => ψ (erasedPath η (cfPocket R L r)
        (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) v))
      (pocketClock η (cfPocket R L r)
        (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))
        (firstHit η (cfArcR R L r 0))) := by
  obtain ⟨hτ0, hτ, hσ, hxf⟩ := corner_firstHits_of_wall_visits h h0 hη.1 hη.2.1 (Or.inl hvisR)
  have havoidB := fun t ht => notMem_image_negInv (havoid t ht)
  have hfaces := gate_faces_leftOuter_of_target_adherence h h0 hO hη hW hW0
    hτ0 hτ hσ hxf hrevR havoidB haccess
  exact R7FaceSelect.relLoewner_leftOuter_of_witnesses h h0 hM hO hcR hcL houter
    hη hW hW0 hηH hψ havoid hrevR hvisR hrevM hvisM h42 hAC
    (fun s hs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂ => (hfaces s hs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂).2.1)
    (fun s hs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂ => (hfaces s hs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂).2.2)

/-- The finite right-outer relative driver from physical target adherence.
The former witness and bulge hypotheses are absent. -/
theorem relLoewner_rightOuter_of_target_adherence {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
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
    (haccess : AllowedTargetAdherence W (cfPocket R L r) (negInv '' rightSideOf (range M))
      (cfArcR R L r 0) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    RelLoewner
      (fun v => ψ (erasedPath η (cfPocket R L r)
        (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) v))
      (pocketClock η (cfPocket R L r)
        (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))
        (firstHit η (cfArcR R L r 0))) := by
  obtain ⟨hτ0, hτ, hσ, hxf⟩ := corner_firstHits_of_wall_visits h h0 hη.1 hη.2.1 (Or.inr hvisL)
  have havoidB := fun t ht => notMem_image_negInv (havoid t ht)
  have hfaces := gate_faces_rightOuter_of_target_adherence h h0 hO hη hW hW0
    hτ0 hτ hσ hxf hrevL havoidB haccess
  exact R7FaceSelect.relLoewner_rightOuter_of_witnesses h h0 hM hO hcR hcL houter
    hη hW hW0 hηH hψ havoid hrevL hvisL hrevM hvisM h42 hAC
    (fun s hs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂ => (hfaces s hs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂).2.1)
    (fun s hs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂ => (hfaces s hs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂).2.2)

end InteractingSLE.Sec7.R7LocalFace
