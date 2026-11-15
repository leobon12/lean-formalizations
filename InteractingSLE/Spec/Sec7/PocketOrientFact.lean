/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketOrientPrem

/-!
# The orientation fact `L r ∈ leftSideOf (range R)` from the left counterflow frontier

Packet PROVE-STRIPSYS20, item 5. Specification §7.4.1, proof of Aux. lemma 130 (`source/spec/p385-432.md` L466–L468,
p. 412): "The selected second arc has a nonempty portion before `r` on the complete left frontier `β`. Both selected
arcs are contained in the full counterflow range. Its exterior left side is connected to the original domain boundary
and is disjoint from those arcs; it cannot be the bounded Jordan side enclosed by them. Consequently `C` is on the range
side of this frontier portion. Thus the second incoming arc is the left boundary of `C` and the first is its right
boundary."

PROVE-STRIPSYS18 reduced the flow-chart orientation of the change pocket (`PocketMarks.IsFlowChartOriented`) to the
single fact that the left wall's change point lies on the left of the right wall
(`IsChangeConfigInc.isFlowChartOriented_of_mem_leftSideOf`). Here that fact is derived, deterministically, from the two
inputs the source uses:

* the left wall coincides with the complete left frontier `β = η_{π/2}` at its change time (`β^{(r)}`'s prefix through
  `r` is `β`'s: "Its prefix through `r` … unchanged");
* the right wall does not enter the open left side of `β` (it lies in the counterflow range, Lemma 5.7, and the
  counterflow range does not meet the exterior left side of its left frontier).

The argument: the left side of `β` is a union of components of `ℍ \ range β`; if it misses `R`, each of its components
is a preconnected subset of `ℍ \ range R` adherent to a negative real, hence lies in the left side of `R`
(`leftSideOf_subset_leftSideOf`). Every point of `β` is adherent to `β`'s left side (`WangWu.mem_closure_leftSideOf`),
so a point of `β` off `R` is adherent to the left side of `R`; it is not on the (open, disjoint) right side, so it is on
the left side (`mem_leftSideOf_of_disjoint`).

## Main results

* `leftSideOf_subset_leftSideOf`, **`mem_leftSideOf_of_disjoint`**;
* **`IsChangeConfigInc.isFlowChartOriented_of_leftFrontier`**: `IsFlowChartOriented R L r` from `L r = β r` and
  `range R ∩ leftSideOf (range β) = ∅`;
* `IsChangeConfigInc.isFlowChartOriented_of_frontier_range`: the same with the right wall in a set `K` (the counterflow
  range) that misses the left side of `β`;
* `ae_isFlowChartOriented`: the random form on a selection event.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function MeasureTheory
open QuantumZipper (H Hbar)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketOrientFact

open WangWu Lemma71I PocketCoord PocketMarks

variable {R L β : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- A simple proper path from `0` meets the real line only at `0`. -/
theorem notMem_range_of_neg (hR : IsSimpleProper R) {x : ℝ} (hx : x < 0) : (x : ℂ) ∉ range R := by
  rintro ⟨t, ht⟩
  rcases eq_zero_or_pos t with rfl | htpos
  · rw [hR.2.2.1] at ht
    have hx0 : x = 0 := by exact_mod_cast ht.symm
    exact absurd hx0 hx.ne
  · have hH := hR.2.2.2.1 t htpos
    rw [ht] at hH
    have him : ((x : ℂ)).im = 0 := ofReal_im x
    exact absurd (show (0 : ℝ) < ((x : ℂ)).im from hH) (by rw [him]; exact lt_irrefl 0)

/-- **The left side of a path that misses `R` lies in the left side of `R`.** Each component of `ℍ \ range β` in the
left side of `β` is a preconnected subset of `ℍ \ range R` adherent to a negative real. -/
theorem leftSideOf_subset_leftSideOf (hR : IsSimpleProper R)
    (hd : Disjoint (range R) (leftSideOf (range β))) : leftSideOf (range β) ⊆ leftSideOf (range R) := by
  intro z hz
  have hsub : connectedComponentIn (H \ range β) z ⊆ H \ range R := fun w hw =>
    ⟨(connectedComponentIn_subset _ _ hw).1, fun hwR =>
      Set.disjoint_left.1 hd hwR (mem_leftSideOf_of_mem_connectedComponentIn hz hw)⟩
  have hzR : z ∈ H \ range R := hsub (mem_connectedComponentIn hz.1)
  obtain ⟨hz1, x, hx, -, hxcl⟩ := hz
  refine ⟨hzR, x, hx, notMem_range_of_neg hR hx, closure_mono ?_ hxcl⟩
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hz1) hsub

/-- **A point of the left frontier off the right wall lies on the left of the right wall**, when the right wall
does not enter the left side of the frontier. -/
theorem mem_leftSideOf_of_disjoint (hR : IsSimpleProper R) (hβ : IsSimpleProper β)
    (hd : Disjoint (range R) (leftSideOf (range β))) {s : ℝ≥0} (hs : 0 < s) (hsR : β s ∉ range R) :
    β s ∈ leftSideOf (range R) := by
  have hcl : β s ∈ closure (leftSideOf (range β)) := by
    have := hβ.isProperArc.mem_closure_leftSideOf (s := (s : ℝ)) (NNReal.coe_pos.2 hs)
    rwa [arcRange_realPath, realPath_coe] at this
  have hcl' := closure_mono (leftSideOf_subset_leftSideOf hR hd) hcl
  have hH : β s ∈ H := hβ.2.2.2.1 s hs
  have hRarc := hR.isProperArc
  rcases hRarc.mem_leftSideOf_or_mem_rightSideOf hH (by rwa [arcRange_realPath]) with h | h
  · rwa [arcRange_realPath] at h
  · exfalso
    have hopen := Sec5.Cond44Ref.isOpen_rightSideOf_arcRange hRarc
    have hdisj := hRarc.disjoint_leftSideOf_rightSideOf
    rw [arcRange_realPath] at hopen hdisj h
    exact Set.disjoint_left.1 (hdisj.closure_left hopen) hcl' h

/-- The right wall in a set `K` that misses the left side of `β` does not enter that side. -/
theorem disjoint_of_subset {K : Set ℂ} (hRK : range R ⊆ K) (hK : Disjoint K (leftSideOf (range β))) :
    Disjoint (range R) (leftSideOf (range β)) :=
  hK.mono_left hRK

/-- The closure of a set missing an open left side still misses it (the completed counterflow range). -/
theorem disjoint_closure_of_disjoint (hβ : IsSimpleProper β) {K : Set ℂ}
    (hK : Disjoint K (leftSideOf (range β))) : Disjoint (closure K) (leftSideOf (range β)) := by
  have hopen := Sec5.Cond44Ref.isOpen_leftSideOf_arcRange hβ.isProperArc
  rw [arcRange_realPath] at hopen
  exact hK.closure_left hopen

/-- **The orientation fact and the flow-chart orientation** (Aux. lemma 130, p. 412): if the left wall's change
point is the point of the left frontier `β` at time `r`, and the right wall does not enter the left side of `β`, then
`L r ∈ leftSideOf (range R)` and every two-point uniformizer of the change pocket sends the right arc to `(0, ∞)`. -/
theorem _root_.InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc.mem_leftSideOf_of_leftFrontier
    (h : IsChangeConfigInc R L r) (hβ : IsSimpleProper β) (hLβ : L r = β r)
    (hd : Disjoint (range R) (leftSideOf (range β))) : L r ∈ leftSideOf (range R) := by
  rw [hLβ]
  exact mem_leftSideOf_of_disjoint h.right hβ hd h.pos (hLβ ▸ h.off)

theorem _root_.InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc.isFlowChartOriented_of_leftFrontier
    (h : IsChangeConfigInc R L r) (hβ : IsSimpleProper β)
    (hLβ : L r = β r) (hd : Disjoint (range R) (leftSideOf (range β))) : IsFlowChartOriented R L r :=
  h.isFlowChartOriented_of_mem_leftSideOf (h.mem_leftSideOf_of_leftFrontier hβ hLβ hd)

/-- The flow-chart orientation from the counterflow range: the right wall lies in `K` (Lemma 5.7's containment) and
`K` misses the exterior left side of its left frontier `β` (non-boundary duality). -/
theorem _root_.InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc.isFlowChartOriented_of_frontier_range
    (h : IsChangeConfigInc R L r) (hβ : IsSimpleProper β)
    (hLβ : L r = β r) {K : Set ℂ} (hRK : range R ⊆ K) (hK : Disjoint K (leftSideOf (range β))) :
    IsFlowChartOriented R L r :=
  h.isFlowChartOriented_of_leftFrontier hβ hLβ (disjoint_of_subset hRK hK)

/-- **The random form**: on a selection event of change configurations, almost surely the change pocket is
flow-chart oriented, as soon as almost surely the left frontier is a simple proper path through the left wall's
change point and the right wall lies in a set (the counterflow range) missing the frontier's left side. -/
theorem ae_isFlowChartOriented {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {R L β : Ω → ℝ≥0 → ℂ}
    {K : Ω → Set ℂ} {G : Set Ω} (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω)) (hLβ : ∀ᵐ ω ∂P, L ω r = β ω r) (hRK : ∀ᵐ ω ∂P, range (R ω) ⊆ K ω)
    (hK : ∀ᵐ ω ∂P, Disjoint (K ω) (leftSideOf (range (β ω)))) :
    ∀ᵐ ω ∂P, ω ∈ G → IsFlowChartOriented (R ω) (L ω) r := by
  filter_upwards [hβ, hLβ, hRK, hK] with ω h1 h2 h3 h4 hω
  exact (hG ω hω).isFlowChartOriented_of_frontier_range h1 h2 h3 h4

end InteractingSLE.Sec7.PocketOrientFact
