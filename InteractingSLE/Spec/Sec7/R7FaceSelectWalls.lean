/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7FaceSelectBoundary

/-!
# The actual outer wall's untouched exterior

PROVE-R7-GAPEQ. Its exterior is preconnected and unbounded after inversion, is disjoint
from the physical pocket frontier, and adheres to the whole selected outer side. Endpoint
adherence uses continuity of the closed clipped side, including an entrance at zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.R7FaceSelect

open WangWu Lemma71I PocketCoord PocketJordan

/-- The left exterior of a simple proper wall is preconnected and unbounded in the
counterflow chart. Zero is adherent to the original side, rather than a point of that side. -/
theorem left_exterior_props {L : ℝ≥0 → ℂ} (hL : IsSimpleProper L) :
    IsPreconnected (negInv '' leftSideOf (range L)) ∧
      negInv '' leftSideOf (range L) ⊆ H ∧
      ¬ IsBounded (negInv '' leftSideOf (range L)) := by
  have hEH : leftSideOf (range L) ⊆ H := fun _ hz => hz.1.1
  have hE : IsPreconnected (leftSideOf (range L)) := by
    simpa only [arcRange_realPath] using hL.isProperArc.isPreconnected_leftSideOf
  have h0 : (0 : ℂ) ∈ closure (leftSideOf (range L)) :=
    R7Outer.range_subset_closure_leftSideOf_self hL ⟨0, hL.2.2.1⟩
  exact ⟨hE.image _ (continuousOn_negInv.mono hEH), PocketJordan.image_negInv_subset_H hEH,
    not_isBounded_image_negInv_of_zero_closure h0
      (fun hz => by simpa [QuantumZipper.H] using hEH hz)⟩

/-- The right exterior has the same three properties. -/
theorem right_exterior_props {R : ℝ≥0 → ℂ} (hR : IsSimpleProper R) :
    IsPreconnected (negInv '' rightSideOf (range R)) ∧
      negInv '' rightSideOf (range R) ⊆ H ∧
      ¬ IsBounded (negInv '' rightSideOf (range R)) := by
  have hEH : rightSideOf (range R) ⊆ H := fun _ hz => hz.1.1
  have hE : IsPreconnected (rightSideOf (range R)) := by
    simpa only [arcRange_realPath] using hR.isProperArc.isPreconnected_rightSideOf
  have h0 : (0 : ℂ) ∈ closure (rightSideOf (range R)) :=
    R7Outer.range_subset_closure_rightSideOf_self hR ⟨0, hR.2.2.1⟩
  exact ⟨hE.image _ (continuousOn_negInv.mono hEH), PocketJordan.image_negInv_subset_H hEH,
    not_isBounded_image_negInv_of_zero_closure h0
      (fun hz => by simpa [QuantumZipper.H] using hEH hz)⟩

/-- A compactified wall point at positive disc time avoids the image of any side disjoint
from the wall. At disc time one the point is zero, outside every inverted half-plane side. -/
theorem cfPt_not_mem_exterior {R : ℝ≥0 → ℂ} {S : Set ℂ} (hR : IsSimpleProper R)
    (hSH : S ⊆ H) (hd : Disjoint (range R) S) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) :
    cfPt (toDisc (realPath R) s) ∉ negInv '' S := by
  rcases lt_or_eq_of_le hs.2 with hs1 | rfl
  · obtain ⟨he, -⟩ := cfPt_toDisc_of_mem hR ⟨hs.1, hs1⟩
    rw [he]
    rintro ⟨z, hz, hez⟩
    have he' : z = R (arcTime s).toNNReal := by
      simpa only [negInv_negInv] using congrArg negInv hez
    exact Set.disjoint_left.1 hd ⟨_, rfl⟩ (he' ▸ hz)
  · rw [toDisc_one, cfPt_one]
    exact fun hz => by simpa [QuantumZipper.H] using PocketJordan.image_negInv_subset_H hSH hz

/-- A closed clipped counterflow arc adheres to an inverted side whenever the full physical
wall adheres to the original side. Continuity supplies both clipped endpoints. -/
theorem cf_clip_subset_closure_exterior {R : ℝ≥0 → ℂ} {A : ℝ → ℂ} {S : Set ℂ}
    {a b : ℝ} (hR : IsSimpleProper R) (hab : a < b) (ha : 0 < a) (hb : b ≤ 1)
    (hA : ContinuousOn A (Icc 0 1))
    (he : ∀ v ∈ Ioo (0 : ℝ) 1, A v = cfPt (toDisc (realPath R) (a + v * (b - a))))
    (hS : range R ⊆ closure S) : A '' Icc 0 1 ⊆ closure (negInv '' S) := by
  have hi : A '' Ioo 0 1 ⊆ closure (negInv '' S) := by
    rintro _ ⟨v, hv, rfl⟩
    let s := a + v * (b - a)
    have hs : s ∈ Ioo (0 : ℝ) 1 :=
      ⟨ha.trans ((IsChangeConfigInc.affine_mem hab).2.1 hv).1,
        ((IsChangeConfigInc.affine_mem hab).2.1 hv).2.trans_le hb⟩
    obtain ⟨hsR, hpos⟩ := cfPt_toDisc_of_mem hR hs
    rw [he v hv, hsR]
    have hne := WangWu.ne_zero_of_mem_H (hR.2.2.2.1 _ hpos)
    exact (WangWu.continuousAt_negInv hne).continuousWithinAt.mem_closure_image (hS ⟨_, rfl⟩)
  have hc : A '' Icc 0 1 ⊆ closure (A '' Ioo 0 1) := by
    have hA' : ContinuousOn A (closure (Ioo (0 : ℝ) 1)) := by
      simpa only [closure_Ioo zero_ne_one] using hA
    simpa only [closure_Ioo zero_ne_one] using hA'.image_closure
  exact hc.trans (closure_minimal hi isClosed_closure)

/-- The whole selected left outer side adheres to its own exterior. -/
theorem cfArcL_subset_closure_exterior {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) :
    cfArcL R L r '' Icc 0 1 ⊆ closure (negInv '' leftSideOf (range L)) := by
  obtain ⟨-, -, -, -, hb, hab, -⟩ := h.changeCorner_props
  exact cf_clip_subset_closure_exterior h.left hab (h.leftLo_pos h0) hb.2
    (h.isCfPocket h0).cont₂ (fun _ _ => rfl) (R7Outer.range_subset_closure_leftSideOf_self h.left)

/-- The whole selected right outer side adheres to its own exterior. -/
theorem cfArcR_subset_closure_exterior {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r)) :
    cfArcR R L r '' Icc 0 1 ⊆ closure (negInv '' rightSideOf (range R)) := by
  obtain ⟨-, hb, hab, -⟩ := h.changeCorner_props
  exact cf_clip_subset_closure_exterior h.right hab (h.rightLo_pos h0) hb.2
    (h.isCfPocket h0).cont₁ (fun _ _ => rfl) (R7Outer.range_subset_closure_rightSideOf_self h.right)

/-- The left exterior misses both complete sides of an ordered change pocket. -/
theorem left_exterior_disjoint_frontier {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L)) :
    Disjoint (negInv '' leftSideOf (range L)) (frontier (cfPocket R L r)) := by
  have hnest : leftSideOf (range L) ⊆ leftSideOf (range R) := by
    simpa only [arcRange_realPath] using
      IsProperArc.leftSideOf_subset_of_disjoint hO.right hO.left hO.right_left
  have hdR : Disjoint (range R) (leftSideOf (range L)) :=
    Set.disjoint_left.2 fun _ hz hL => (hnest hL).1.2 hz
  have hdL : Disjoint (range L) (leftSideOf (range L)) :=
    Set.disjoint_left.2 fun _ hz hL => hL.1.2 hz
  obtain ⟨-, hbR, habR, -, hbL, habL, -⟩ := h.changeCorner_props
  rw [(h.isCfPocket h0).frontier_eq]
  refine Set.disjoint_left.2 ?_
  rintro z hz (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
  · exact cfPt_not_mem_exterior h.right (fun _ hw => hw.1.1) hdR
      ⟨(h.rightLo_pos h0).trans_le ((IsChangeConfigInc.affine_mem habR).1 hv).1,
        ((IsChangeConfigInc.affine_mem habR).1 hv).2.trans hbR.2⟩ hz
  · exact cfPt_not_mem_exterior h.left (fun _ hw => hw.1.1) hdL
      ⟨(h.leftLo_pos h0).trans_le ((IsChangeConfigInc.affine_mem habL).1 hv).1,
        ((IsChangeConfigInc.affine_mem habL).1 hv).2.trans hbL.2⟩ hz

/-- The right exterior misses both complete sides of an ordered change pocket. -/
theorem right_exterior_disjoint_frontier {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L)) :
    Disjoint (negInv '' rightSideOf (range R)) (frontier (cfPocket R L r)) := by
  have hdR : Disjoint (range R) (rightSideOf (range R)) :=
    Set.disjoint_left.2 fun _ hz hR => hR.1.2 hz
  have hdL : Disjoint (range L) (rightSideOf (range R)) := by
    simpa only [arcRange_realPath] using hO.right_left
  obtain ⟨-, hbR, habR, -, hbL, habL, -⟩ := h.changeCorner_props
  rw [(h.isCfPocket h0).frontier_eq]
  refine Set.disjoint_left.2 ?_
  rintro z hz (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
  · exact cfPt_not_mem_exterior h.right (fun _ hw => hw.1.1) hdR
      ⟨(h.rightLo_pos h0).trans_le ((IsChangeConfigInc.affine_mem habR).1 hv).1,
        ((IsChangeConfigInc.affine_mem habR).1 hv).2.trans hbR.2⟩ hz
  · exact cfPt_not_mem_exterior h.left (fun _ hw => hw.1.1) hdL
      ⟨(h.leftLo_pos h0).trans_le ((IsChangeConfigInc.affine_mem habL).1 hv).1,
        ((IsChangeConfigInc.affine_mem habL).1 hv).2.trans hbL.2⟩ hz

end InteractingSLE.Sec7.R7FaceSelect
