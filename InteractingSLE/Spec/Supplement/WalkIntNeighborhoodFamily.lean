/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntNeighborhoodBoundary

/-!
# Retained families with constructed incident intervals and landings

A supported neighborhood of one common coordinate for the base prefix
supplies all interval fields. Raw base inclusion propagates this coordinate
to every retained pair. A physical frontier collar proves that neighborhood.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntNeighborhood

open WalkIntFill WalkIntActive WalkMean

/-- Construct the existing retained family from one interior coordinate.
Its intervals, openness, connectedness, anchor membership and landings are
conclusions. The remaining exit selection is the physical tail condition. -/
def retainedExitGeometry {c : Chart} {sR sL : ExplState} {α β : ℝ≥0 → ℂ}
    (pair : ℕ → RetainedPair sR sL) (anchor : ℝ) {R L C : Set ℂ}
    (hchart : IsComponentChart R L C c) (hCo : IsOpen C)
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    {wR wL : ExplSpec} (hR : range α = physOf wR sR) (hL : range β = physOf wL sL)
    (hbase : ∀ i, (pair 0).raw ⊆ (pair i).raw)
    (hTail : Bornology.IsBounded (c.dom : Set ℂ) → ∀ i, ∃ s t : ℝ≥0,
      0 < s ∧ 0 < t ∧ α s = β t ∧
        Disjoint (closure (pair i).right.raw) (α '' Ici s) ∧
        Disjoint (closure (pair i).left.raw) (β '' Ici t) ∧ α s ∈ closure (c.dom : Set ℂ))
    (hEntry : anchor ∈ interior (landingCoordinates c (pair 0).raw)) :
    RetainedExitGeometry c sR sL α β where
  pair := pair
  before := fun hb i =>
    (WalkIntEnvelope.beforeExit_iff_tail_separation (pair i) hα hβ hR hL).2 (hTail hb i)
  interval := fun i => incidentInterval c (pair i).raw anchor
  anchor := anchor
  isOpen := fun i => isOpen_incidentInterval c (pair i).raw anchor
  isPreconnected := fun i => isPreconnected_incidentInterval c (pair i).raw anchor
  anchor_mem := fun i => anchor_mem_incidentInterval
    (interior_mono (landingCoordinates_mono c (hbase i)) hEntry)
  landing := fun _ _ hx => landing_of_mem_interval hchart hCo hx
  base_raw := hbase

/-- A single physical frontier collar constructs the interval and landing
data for all retained indices. The resulting integer is common to them all. -/
theorem exists_int_of_frontier_collar {c : Chart} {sR sL : ExplState}
    {α β : ℝ≥0 → ℂ} (pair : ℕ → RetainedPair sR sL) (anchor : ℝ)
    {R L C : Set ℂ} (hchart : IsComponentChart R L C c) (hCo : IsOpen C)
    (hc : c.IsConformal) (hLift : c.HasDerivLift)
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {wR wL : ExplSpec} (hR : range α = physOf wR sR) (hL : range β = physOf wL sL)
    (hC : (c.dom : Set ℂ) ∈ betweenComponents (physOf wR sR) (physOf wL sL))
    (hbase : ∀ i, (pair 0).raw ⊆ (pair i).raw)
    (hTail : Bornology.IsBounded (c.dom : Set ℂ) → ∀ i, ∃ s t : ℝ≥0,
      0 < s ∧ 0 < t ∧ α s = β t ∧
        Disjoint (closure (pair i).right.raw) (α '' Ici s) ∧
        Disjoint (closure (pair i).left.raw) (β '' Ici t) ∧ α s ∈ closure (c.dom : Set ℂ))
    {r : ℝ} (hr : 0 < r)
    (hcover : frontier (c.dom : Set ℂ) ∩
      ball (GW4Traverse.invExt c (anchor : ℂ)) r ⊆
        closure (pair 0).raw ∪ {z : ℂ | z.im = 0}) :
    ∃ n : ℤ, ∀ i x, x ∈ incidentInterval c (pair i).raw anchor →
      Tendsto (fun y => (pair i).chart.2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  have ha := anchor_mem_interior_of_frontier_collar hchart hCo hc hr hcover
  exact (retainedExitGeometry pair anchor hchart hCo hα hβ hR hL hbase hTail ha).exists_int
    hα hβ horder hR hL hC hc hLift

end InteractingSLE.Theorem14.WalkIntNeighborhood
