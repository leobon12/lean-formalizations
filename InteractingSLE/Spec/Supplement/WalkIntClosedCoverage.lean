/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntClosedLanding
import InteractingSLE.Spec.Supplement.WalkIntWallCoverage

/-!
# One integer and cofinal canonical intervals for completed-prefix families

Physical collars and raw nesting construct the anchor and every incident
interval. Active containment is proved from the explicitly retained
bounded-case tail input. The analytic integer is supplied by the existing
landing-family theorem, now also for completed finite ordinary pieces.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntClosed

open WalkBdry WalkMean WalkIntNeighborhood WalkIntWall

/-- The only bounded-case geometric input is hTail, with its exact
physical type below. All local collars, active charts, incident intervals
and derivative-lift compatibility are then assembled into one integer. -/
theorem exists_shifted_closed_family_of_local_containment {c : Chart} {sR sL : ExplState}
    {α β : ℝ≥0 → ℂ} (pair : ℕ → ClosedPair sR sL) (anchor : ℝ)
    {R L C : Set ℂ} (hchart : IsComponentChart R L C c) (hCo : IsOpen C)
    (hc : c.IsConformal) (hLift : c.HasDerivLift)
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {wR wL : ExplSpec} (hR : range α = physOf wR sR) (hL : range β = physOf wL sL)
    (hC : (c.dom : Set ℂ) ∈ betweenComponents (physOf wR sR) (physOf wL sL))
    (hmono : Monotone (fun i => (pair i).raw))
    (hTail : Bornology.IsBounded (c.dom : Set ℂ) → ∀ i, ∃ s t : ℝ≥0,
      0 < s ∧ 0 < t ∧ α s = β t ∧
        Disjoint (closure (pair i).right.raw) (α '' Ici s) ∧
        Disjoint (closure (pair i).left.raw) (β '' Ici t) ∧ α s ∈ closure (c.dom : Set ℂ))
    (hLocal : ∀ x : ℝ, ∃ i : ℕ, ∃ r : ℝ, 0 < r ∧
      (wsetOf sR ∪ wsetOf sL) ∩ ball (GW4Traverse.invExt c (x : ℂ)) r ⊆ (pair i).raw) :
    ∃ k : ℕ, ∃ n : ℤ,
      (∀ i x, x ∈ incidentInterval c (pair (i + k)).raw anchor →
        Tendsto (fun y => (pair (i + k)).chart.2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
          (𝓝[H] (x : ℂ)) (𝓝 (2 * Real.pi * n))) ∧
      ∀ (x : ℝ) (lower : ℕ), ∃ i, lower ≤ i ∧
        uIcc anchor x ⊆ incidentInterval c (pair (i + k)).raw anchor := by
  obtain ⟨k, r, hr, hroot⟩ := hLocal anchor
  let Q : ℕ → ClosedPair sR sL := fun i => pair (i + k)
  have hmonoQ : Monotone (fun i => (Q i).raw) := fun i j hij =>
    hmono (Nat.add_le_add_right hij k)
  have hrootQ : (wsetOf sR ∪ wsetOf sL) ∩
      ball (GW4Traverse.invExt c (anchor : ℂ)) r ⊆ (Q 0).raw := by
    simpa only [Q, Nat.zero_add] using hroot
  have hActive (i : ℕ) : (c.dom : Set ℂ) ⊆ H \ fillH (Q i).raw := by
    by_cases hb : Bornology.IsBounded (c.dom : Set ℂ)
    · have hC' : (c.dom : Set ℂ) ∈ betweenComponents (range α) (range β) := by
        rw [hR, hL]
        exact hC
      exact active_closedPair_of_tail_separation (Q i) hα hβ horder hR hL hC'
        (hTail hb (i + k))
    · exact active_closedPair_of_unbounded (Q i) hC c.dom.isOpen hb
  have hcover := frontier_collar_of_ordinary_cover hα hβ hR hL hC hrootQ
  have hEntry := anchor_mem_interior_of_frontier_collar hchart hCo hc hr hcover
  obtain ⟨n, hn⟩ := exists_int_of_closed_landing Q anchor hchart hCo
    (fun i => hmonoQ (Nat.zero_le i)) hActive hEntry hc hLift
  have hLocalQ : ∀ x : ℝ, ∃ i : ℕ, ∃ r : ℝ, 0 < r ∧
      (wsetOf sR ∪ wsetOf sL) ∩ ball (GW4Traverse.invExt c (x : ℂ)) r ⊆ (Q i).raw := by
    intro x
    obtain ⟨i, r, hr, hloc⟩ := hLocal x
    exact ⟨i, r, hr, hloc.trans (hmono (Nat.le_add_right i k))⟩
  refine ⟨k, n, hn, ?_⟩
  intro x lower
  apply exists_incidentInterval_cover_uIcc_ge c (fun i => (Q i).raw) hmonoQ anchor x lower
  intro y _
  obtain ⟨i, r, hr, hloc⟩ := hLocalQ y
  exact ⟨i, anchor_mem_interior_of_frontier_collar hchart hCo hc hr
    (frontier_collar_of_ordinary_cover hα hβ hR hL hC hloc)⟩

end InteractingSLE.Theorem14.WalkIntClosed
