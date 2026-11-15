/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7FaceSelectFaces

/-!
# Finite mixed gaps with the global-side and boundary inputs discharged

PROVE-R7-GAPEQ. First-hit data come from the contained wall's full visits. The two
remaining geometric hypotheses are exactly `GateWitnesses` and `GateBulges`. The contained
attachment input keeps its existing type for the germ-comparison worker.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.R7FaceSelect

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7GapEqCorner R7GateBridge

/-- Full visits of either wall supply the first entrance and the fresh terminal corner. -/
theorem corner_firstHits_of_wall_visits {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {η : ℝ → ℂ}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hη0 : η 0 = 0) (hη : ContinuousOn η (Ici 0))
    (hvis : IsWallVisited R η ∨ IsWallVisited L η) :
    0 ≤ firstHit η (cfArcR R L r 1) ∧
      η (firstHit η (cfArcR R L r 1)) = cfArcR R L r 1 ∧
      η (firstHit η (cfArcR R L r 0)) = cfArcR R L r 0 ∧
      cfArcR R L r 0 ∉ η '' Ico 0 (firstHit η (cfArcR R L r 0)) := by
  have hC := h.isCfPocket h0
  have hcorners : (∃ t, cfArcR R L r 0 ∈ η '' Icc 0 t) ∧
      ∃ t, cfArcR R L r 1 ∈ η '' Icc 0 t := by
    rcases hvis with hR | hL
    · obtain ⟨-, hb, hab, -⟩ := h.changeCorner_props
      constructor
      · simpa only [cfArcR, zero_mul, add_zero] using
          wall_visited hη0 h.right hR ⟨h.rightLo_pos h0, hab.le.trans hb.2⟩
      · simpa only [cfArcR, one_mul, add_sub_cancel] using
          wall_visited hη0 h.right hR ⟨(h.rightLo_pos h0).trans hab, hb.2⟩
    · obtain ⟨-, -, -, -, hb, hab, -⟩ := h.changeCorner_props
      constructor
      · rw [← hC.junction]
        simpa only [cfArcL, zero_mul, add_zero] using
          wall_visited hη0 h.left hL ⟨h.leftLo_pos h0, hab.le.trans hb.2⟩
      · rw [← hC.seed]
        simpa only [cfArcL, one_mul, add_sub_cancel] using
          wall_visited hη0 h.left hL ⟨(h.leftLo_pos h0).trans hab, hb.2⟩
  obtain ⟨hτ0, hτ, -⟩ := firstHit_spec hη hcorners.2
  obtain ⟨-, hσ, hxf⟩ := firstHit_spec hη hcorners.1
  exact ⟨hτ0, hτ, hσ, hxf⟩

/-- **The left-outer physical gap**, with all former global-side hypotheses discharged.
`hwitness` and `hbulges` are the remaining planar inputs; `hAC` is the unchanged contained
attachment input. No physical gap equality or erasure fact is assumed. -/
theorem pocketGapEq_leftOuter_of_witnesses {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H) (hrev : IsWallReverseVisit R η) (hvis : IsWallVisited R η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcR R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M))
    (hwitness : GateWitnesses W η (cfArcR R L r) (cfArcL R L r) (cfPocket R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (hbulges : GateBulges W η (cfArcR R L r) (cfArcL R L r)
      (cfPocket R L r) (negInv '' leftSideOf (range M))
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    PocketGapEq η (cfPocket R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) := by
  obtain ⟨hτ0, hτ, hσ, hxf⟩ := corner_firstHits_of_wall_visits h h0 hη.1 hη.2.1 (Or.inl hvis)
  have havoidB := fun t ht => notMem_image_negInv (havoid t ht)
  exact pocketGapEq_leftOuter_of_faces h h0 hη hW hW0 hηH hrev hvis h42 hAC havoidB
    (changePocket_subset_right_of_order h hO) (left_exterior_subset hO)
    (gate_faces_leftOuter h h0 hO hη hW hW0 hτ0 hτ hσ hxf hrev havoidB hwitness hbulges)

/-- **The reflected right-outer physical gap**, with the contained left side listed first
in the witness and bulge inputs. -/
theorem pocketGapEq_rightOuter_of_witnesses {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H) (hrev : IsWallReverseVisit L η) (hvis : IsWallVisited L η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcL R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M))
    (hwitness : GateWitnesses W η (cfArcL R L r) (cfArcR R L r) (cfPocket R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (hbulges : GateBulges W η (cfArcL R L r) (cfArcR R L r)
      (cfPocket R L r) (negInv '' rightSideOf (range M))
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    PocketGapEq η (cfPocket R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) := by
  obtain ⟨hτ0, hτ, hσ, hxf⟩ := corner_firstHits_of_wall_visits h h0 hη.1 hη.2.1 (Or.inr hvis)
  have havoidB := fun t ht => notMem_image_negInv (havoid t ht)
  exact pocketGapEq_rightOuter_of_faces h h0 hη hW hW0 hηH hrev hvis h42 hAC havoidB
    (changePocket_subset_left_of_order h hO) (right_exterior_subset hO)
    (gate_faces_rightOuter h h0 hO hη hW hW0 hτ0 hτ hσ hxf hrev havoidB hwitness hbulges)

end InteractingSLE.Sec7.R7FaceSelect
