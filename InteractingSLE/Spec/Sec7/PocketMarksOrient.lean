/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketMarks
import InteractingSLE.Spec.Supplement.GW3Orient

/-!
# The boundary orientation of the change pocket's flow chart from the side of the right wall

Packet PROVE-STRIPSYS17 (specification §7.4, Aux. lemma 119, p. 385: "Let `C` be the Jordan pocket between two
consecutive common contacts `x₀, y₀`, with `α_R` on its right and `α_L` on its left […] The left incoming arc maps to
`ℝ₋` and the right one to `ℝ₊`").

`PocketMarks.IsFlowChartOriented` (every two-point uniformizer of the Cayley image of the change pocket sends the open
right-wall arc into `(0, ∞)`) follows from the two topological premises of the orientation theorem of PROVE-ORIENT
(`Prop74B.re_pos_of_crossLoop`): the pocket lies on the left of the right-wall crosscut (winding number `1` of its
closing loop; for instance `C ⊆ leftSideOf (range R)`, `GW3.windNum_crossLoop_of_subset_leftSideOf`), and the open
right-wall arc is reached from the right (an unbounded preconnected set off the closed pocket, the wall and the upper
semicircle, adherent to a point of the open arc). No global order of the walls is needed.

## Main results

* **`IsChangeConfigInc.isFlowChartOriented_of_crossLoop`**;
* **`IsChangeConfigInc.isFlowChartOriented_of_leftSideOf`**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.Orientation (windNum crossLoop)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc

open WangWu Lemma71I PocketJordan PocketMarks

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **The flow-chart orientation from the crosscut loop** (`Prop74B.re_pos_of_crossLoop`): if the Cayley image of the
change pocket has winding number `1` with respect to the closed right-wall crosscut loop and the open right-wall arc is
reached from the right, every two-point uniformizer sends the open right-wall arc into `(0, ∞)`. -/
theorem isFlowChartOriented_of_crossLoop (h : IsChangeConfigInc R L r)
    (hleft : ∀ z ∈ cayley '' changePocket R L r, windNum (crossLoop (toDisc (realPath R))) z = 1)
    (hright : ∃ p ∈ toDisc (realPath R) '' Ioo (rightLo R L r) (rightHi R L r), p ∉ semiArc 1 ∧
      ∃ V : Set ℂ, IsPreconnected V ∧ ¬ IsBounded V ∧ p ∈ closure V ∧
        Disjoint V (closure (cayley '' changePocket R L r) ∪ toDisc (realPath R) '' Icc 0 1 ∪ semiArc 1)) :
    IsFlowChartOriented R L r := by
  intro Ψ hU
  obtain ⟨hg, -, -, -, -, hC⟩ := h.changeCorners
  obtain ⟨hu, hv, huv, -⟩ := h.changeCorner_props
  have hαR := h.isDiscCrosscut_right
  obtain ⟨-, -, hdisj, -, -⟩ := pocket_props_of_strictMono hαR h.isDiscCrosscut_left h.inc hg
  obtain ⟨-, -, -, hI, -⟩ := h.isMarkedPocket
  have hCα : ∀ x ∈ changePocket R L r, cayley x ∉ toDisc (realPath R) '' Icc 0 1 := fun x hx hm => by
    have hD : cayley x ∈ cayley '' changePocket R L r := mem_image_of_mem _ hx
    rw [hC] at hD
    exact Set.disjoint_left.1 hdisj hD (Or.inl hm)
  exact Prop74B.re_pos_of_crossLoop hαR.cont hαR.inj hαR.zero hαR.one h.isOpen_changePocket
    h.isConnected_changePocket.isPreconnected h.changePocket_subset_H hCα hu.1 huv hv.2 hI
    (isConformalBijection_comp hU.conf (Lemma71F.isConformalBijection_cayley_image h.changePocket_subset_H))
    hU.cont hU.inj hU.mapsTo hU.zero hU.tendsto (fun _ _ => rfl) hleft hright

/-- **The flow-chart orientation from the side of the right wall**: if the change pocket lies on the left of the right
wall (`C ⊆ leftSideOf (range R)`, Aux. lemma 119: "with `α_R` on its right") and the open right-wall arc is reached
from the right, every two-point uniformizer sends the open right-wall arc into `(0, ∞)`. -/
theorem isFlowChartOriented_of_leftSideOf (h : IsChangeConfigInc R L r)
    (hCl : changePocket R L r ⊆ leftSideOf (range R))
    (hright : ∃ p ∈ toDisc (realPath R) '' Ioo (rightLo R L r) (rightHi R L r), p ∉ semiArc 1 ∧
      ∃ V : Set ℂ, IsPreconnected V ∧ ¬ IsBounded V ∧ p ∈ closure V ∧
        Disjoint V (closure (cayley '' changePocket R L r) ∪ toDisc (realPath R) '' Icc 0 1 ∪ semiArc 1)) :
    IsFlowChartOriented R L r :=
  h.isFlowChartOriented_of_crossLoop
    (Theorem14.GW3.windNum_crossLoop_of_subset_leftSideOf h.right.isProperCurve h.right.2.2.1 hCl) hright

end InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc
