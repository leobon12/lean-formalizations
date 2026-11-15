/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntNeighborhoodFamily

/-!
# Between-component frontiers lie on the ordinary walls or the real line

The frontier statement for components of open sets is already proved.
Specialize it to the complement of two closed physical walk ranges, then
use the existing ordinary/physical identity inside the upper half-plane.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntWall

/-- No additional component-shape input is needed for this frontier
inclusion. Real frontier values are retained without an exceptional set. -/
theorem frontier_between_subset {R L C : Set ℂ} (hR : IsClosed R) (hL : IsClosed L)
    (hC : C ∈ betweenComponents R L) :
    frontier C ⊆ ((R ∪ L) ∩ H) ∪ {z : ℂ | z.im = 0} := by
  obtain ⟨a, -, -, -, rfl⟩ := hC
  have hopen : IsOpen (H \ (R ∪ L)) := QuantumZipper.isOpen_H.sdiff (hR.union hL)
  intro z hz
  have hout := frontier_connectedComponentIn_subset_compl hopen a hz
  by_cases hzH : z ∈ H
  · left
    exact ⟨not_not.1 (fun h => hout ⟨hzH, h⟩), hzH⟩
  · right
    have hclH : z ∈ closure H := closure_mono
      (fun w hw => (connectedComponentIn_subset _ _ hw).1) (frontier_subset_closure hz)
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar] at hclH
    exact le_antisymm (not_lt.1 hzH) hclH

/-- Proper full-walk parametrizations make the physical ranges closed.
Their frontier contribution in H is exactly the ordinary recorded union. -/
theorem frontier_between_walks_subset {sR sL : ExplState} {wR wL : ExplSpec}
    {α β : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (hR : range α = WalkMean.physOf wR sR) (hL : range β = WalkMean.physOf wL sL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (WalkMean.physOf wR sR) (WalkMean.physOf wL sL)) :
    frontier C ⊆ (WalkBdry.wsetOf sR ∪ WalkBdry.wsetOf sL) ∪ {z : ℂ | z.im = 0} := by
  have hRc : IsClosed (WalkMean.physOf wR sR) := by
    rw [← hR]
    exact (WalkCont.isClosedEmbedding_of_isProperCurve hα).isClosed_range
  have hLc : IsClosed (WalkMean.physOf wL sL) := by
    rw [← hL]
    exact (WalkCont.isClosedEmbedding_of_isProperCurve hβ).isClosed_range
  have hfront := frontier_between_subset hRc hLc hC
  rw [union_inter_distrib_right, WalkIntFiber.physOf_inter_H,
    WalkIntFiber.physOf_inter_H] at hfront
  exact hfront

end InteractingSLE.Theorem14.WalkIntWall
