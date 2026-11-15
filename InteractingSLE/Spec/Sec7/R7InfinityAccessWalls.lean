/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityAccessExterior

/-!
# The actual infinite outer arms adhere to their untouched exteriors

PROVE-R7-GAPEQ. Ordered wall sides give exterior exclusion from the closed pocket.
The proper clipped outer arm, including its start, adheres to that exterior.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.R7InfinityAccess

open Sec6 WangWu Lemma71I PocketCoord PocketJordan

/-- Inverting an open exterior disjoint from a pocket preserves exclusion from
the closed pocket. Openness, rather than pocket boundedness, is sufficient. -/
theorem inverted_exterior_subset_compl_closure {C E : Set ℂ}
    (hEo : IsOpen E) (hEH : E ⊆ H) (hd : Disjoint E C) :
    negInv '' E ⊆ (closure (negInv '' C))ᶜ := by
  have hd' : Disjoint (negInv '' E) (negInv '' C) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, he⟩
    have he' : w = z := by simpa only [negInv_negInv] using congrArg negInv he
    exact Set.disjoint_left.1 hd hz (he' ▸ hw)
  exact Set.disjoint_left.1 (hd'.closure_right (isOpen_image_negInv' hEo hEH))

/-- A proper clipped wall arm adheres to the inverted wall side. Its start is
included by continuity, even if it is the counterflow seed zero. -/
theorem proper_clip_subset_closure_exterior {X : ℝ≥0 → ℂ} {A : ℝ → ℂ} {S : Set ℂ} {b : ℝ}
    (hX : IsSimpleProper X) (hb : 0 < b) (hb1 : b ≤ 1)
    (hAc : ContinuousOn A (Ici 0))
    (hA : ∀ v ∈ Ioi (0 : ℝ), A v = cfPt (toDisc (realPath X) (b / (1 + v))))
    (hS : range X ⊆ closure S) : A '' Ici 0 ⊆ closure (negInv '' S) := by
  have hi : A '' Ioi 0 ⊆ closure (negInv '' S) := by
    rintro _ ⟨v, hv, rfl⟩
    have hv0 : 0 < v := hv
    have hv1 : 0 < 1 + v := by linarith only [hv0]
    have hs : b / (1 + v) ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos hb hv1, (div_lt_one hv1).2 (by linarith only [hb1, hv0])⟩
    obtain ⟨he, hpos⟩ := cfPt_toDisc_of_mem hX hs
    rw [hA v hv, he]
    exact (WangWu.continuousAt_negInv
      (WangWu.ne_zero_of_mem_H (hX.2.2.2.1 _ hpos))).continuousWithinAt.mem_closure_image
      (hS ⟨_, rfl⟩)
  have hc : A '' Ici 0 ⊆ closure (A '' Ioi 0) := by
    have hAc' : ContinuousOn A (closure (Ioi (0 : ℝ))) := by rwa [closure_Ioi]
    simpa only [closure_Ioi] using hAc'.image_closure
  exact hc.trans (closure_minimal hi isClosed_closure)

/-- The left outer wall supplies all physical exterior data at infinity. -/
theorem left_outer_exterior_props {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L)) :
    let E := negInv '' leftSideOf (range L);
    IsPreconnected E ∧ E ⊆ H ∧ ¬ IsBounded E ∧
      E ⊆ (closure (cfPocket R L r))ᶜ ∧ cfArcLInf R L r '' Ici 0 ⊆ closure E := by
  obtain ⟨hE, hEH, hEb⟩ := R7FaceSelect.left_exterior_props h.left
  have hLc : IsClosed (range L) := by
    simpa only [arcRange_realPath] using h.left.isProperArc.isClosed_arcRange
  have hEo := Theorem14.SB.isOpen_leftSideOf
    (fun z hz => hLc.closure_eq ▸ hz.1)
  have hd : Disjoint (leftSideOf (range L)) (changePocket R L r) := by
    have hside := h.left.isProperArc.disjoint_leftSideOf_rightSideOf
    rw [arcRange_realPath] at hside
    exact hside.mono_right (R7FaceSelect.changePocket_subset_right_of_order h hO)
  obtain ⟨-, -, -, -, hhi, hlt, -⟩ := h.changeCorner_props
  have hb : 0 < leftHi R L r := by rwa [h.leftLo_eq_zero_of_rightLo_eq_zero h0] at hlt
  exact ⟨hE, hEH, hEb, inverted_exterior_subset_compl_closure hEo (fun _ hz => hz.1.1) hd,
    proper_clip_subset_closure_exterior h.left hb hhi.2 (h.isCfPocketInf h0).cont₂
      (fun _ _ => rfl) (R7Outer.range_subset_closure_leftSideOf_self h.left)⟩

/-- The reflected right outer wall has the same exterior data, with its own
proper arm and its own right side. -/
theorem right_outer_exterior_props {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L)) :
    let E := negInv '' rightSideOf (range R);
    IsPreconnected E ∧ E ⊆ H ∧ ¬ IsBounded E ∧
      E ⊆ (closure (cfPocket R L r))ᶜ ∧ cfArcRInf R L r '' Ici 0 ⊆ closure E := by
  obtain ⟨hE, hEH, hEb⟩ := R7FaceSelect.right_exterior_props h.right
  have hRc : IsClosed (range R) := by
    simpa only [arcRange_realPath] using h.right.isProperArc.isClosed_arcRange
  have hEo := Theorem14.SB.isOpen_rightSideOf
    (fun z hz => hRc.closure_eq ▸ hz.1)
  have hd : Disjoint (rightSideOf (range R)) (changePocket R L r) := by
    have hside := h.right.isProperArc.disjoint_leftSideOf_rightSideOf
    rw [arcRange_realPath] at hside
    exact hside.symm.mono_right (R7FaceSelect.changePocket_subset_left_of_order h hO)
  obtain ⟨-, hhi, hlt, -⟩ := h.changeCorner_props
  have hb : 0 < rightHi R L r := by rwa [h0] at hlt
  exact ⟨hE, hEH, hEb, inverted_exterior_subset_compl_closure hEo (fun _ hz => hz.1.1) hd,
    proper_clip_subset_closure_exterior h.right hb hhi.2 (h.isCfPocketInf h0).cont₁
      (fun _ _ => rfl) (R7Outer.range_subset_closure_rightSideOf_self h.right)⟩

end InteractingSLE.Sec7.R7InfinityAccess
