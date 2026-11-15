/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GateBridgeErasure
import InteractingSLE.Spec.Sec7.PocketOrientFact
import InteractingSLE.Spec.Sec7.Aux119HeightsSide

/-!
# Global order supplies the remaining mixed-pocket side inclusions

PROVE-R7-GAPEQ. Reuse the nesting of sides of ordered proper arcs. Both sides of the
change pocket and both forbidden-side inclusions follow from the source three-wall order.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.R7FaceSelect

open WangWu Lemma71I PocketCoord PocketJordan

/-- The exterior of the left wall is contained in the certified middle wall's exterior. -/
theorem left_exterior_subset {R M L : ℝ≥0 → ℂ}
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L)) :
    negInv '' leftSideOf (range L) ⊆ negInv '' leftSideOf (range M) := by
  apply image_mono
  simpa only [arcRange_realPath] using
    IsProperArc.leftSideOf_subset_of_disjoint hO.middle hO.left hO.middle_left

/-- The exterior of the right wall is contained in the certified middle wall's exterior. -/
theorem right_exterior_subset {R M L : ℝ≥0 → ℂ}
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L)) :
    negInv '' rightSideOf (range R) ⊆ negInv '' rightSideOf (range M) := by
  apply image_mono
  simpa only [arcRange_realPath] using
    SeedField.rightSideOf_subset_of_disjoint hO.right hO.middle hO.right_middle

/-- Ordered walls put the change pocket on the left of its right wall. -/
theorem changePocket_subset_left_of_order {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r)
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L)) :
    changePocket R L r ⊆ leftSideOf (range R) := by
  have hnest : leftSideOf (range L) ⊆ leftSideOf (range R) := by
    simpa only [arcRange_realPath] using
      IsProperArc.leftSideOf_subset_of_disjoint hO.right hO.left hO.right_left
  have hd : Disjoint (range R) (leftSideOf (range L)) := Set.disjoint_left.2
    fun _ hz hL => (hnest hL).1.2 hz
  exact h.changePocket_subset_leftSideOf (h.mem_leftSideOf_of_leftFrontier h.left rfl hd)

/-- The same order gives the flow-chart orientation, with no extra chart premise. -/
theorem flowChartOriented_of_order {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r)
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L)) :
    PocketMarks.IsFlowChartOriented R L r :=
  h.isFlowChartOriented_of_mem_leftSideOf
    (h.changePocket_subset_leftSideOf_iff.mp (changePocket_subset_left_of_order h hO))

/-- Ordered walls put the change pocket on the right of its left wall. -/
theorem changePocket_subset_right_of_order {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r)
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L)) :
    changePocket R L r ⊆ rightSideOf (range L) :=
  h.changePocket_subset_rightSideOf_left (flowChartOriented_of_order h hO)

end InteractingSLE.Sec7.R7FaceSelect
