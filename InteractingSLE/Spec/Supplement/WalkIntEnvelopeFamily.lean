/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntEnvelopeRetained

/-!
# One common integer from physical tail separation

The retained-family theorem now uses only the geometric exit selection
and the existing incidence data. The cutoffs, active containment and joint
properness are proved by the preceding modules and the committed family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntEnvelope

open WalkIntFill WalkIntActive WalkMean

/-- One integer precedes all retained indices and incident coordinates.
The bounded-component selection is precisely physical tail separation;
the unbounded branch needs no exit. No capped-history premise occurs. -/
theorem exists_int_of_tail_separation {c : Chart} {sR sL : ExplState}
    {α β : ℝ≥0 → ℂ} (pair : ℕ → RetainedPair sR sL)
    (interval : ℕ → Set ℝ) (anchor : ℝ)
    (hopen : ∀ i, IsOpen (interval i))
    (hconn : ∀ i, IsPreconnected (interval i)) (hanchor : ∀ i, anchor ∈ interval i)
    (hland : ∀ i x, x ∈ interval i → ∃ p : ℂ,
      (p ∈ closure (pair i).raw ∨ p.im = 0) ∧
        Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p))
    (hbase : ∀ i, (pair 0).raw ⊆ (pair i).raw)
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {wR wL : ExplSpec} (hR : range α = physOf wR sR) (hL : range β = physOf wL sL)
    (hC : (c.dom : Set ℂ) ∈ betweenComponents (physOf wR sR) (physOf wL sL))
    (hTail : Bornology.IsBounded (c.dom : Set ℂ) → ∀ i, ∃ s t : ℝ≥0,
      0 < s ∧ 0 < t ∧ α s = β t ∧
        Disjoint (closure (pair i).right.raw) (α '' Ici s) ∧
        Disjoint (closure (pair i).left.raw) (β '' Ici t) ∧ α s ∈ closure (c.dom : Set ℂ))
    (hc : c.IsConformal) (hLift : c.HasDerivLift) :
    ∃ n : ℤ, ∀ i x, x ∈ interval i →
      Tendsto (fun y => (pair i).chart.2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  let G : RetainedExitGeometry c sR sL α β :=
    { pair := pair
      before := fun hb i =>
        (beforeExit_iff_tail_separation (pair i) hα hβ hR hL).2 (hTail hb i)
      interval := interval
      anchor := anchor
      isOpen := hopen
      isPreconnected := hconn
      anchor_mem := hanchor
      landing := hland
      base_raw := hbase }
  exact G.exists_int hα hβ horder hR hL hC hc hLift

end InteractingSLE.Theorem14.WalkIntEnvelope
