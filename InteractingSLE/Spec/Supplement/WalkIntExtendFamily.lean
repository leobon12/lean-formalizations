/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntExtendRetained

/-!
# Retained incident families with joint properness discharged

The remaining named input concerns physical incidence and the original
target component. Proper inverse extension is constructed for each pair.
The preceding family theorem then gives one integer for all matches.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntExtend

open WalkIntFill

/-- Exact remaining physical incidence data. Joint properness is proved
above and is deliberately absent from this named conditional input. -/
structure RetainedIncidentGeometry (c : Chart) (sR sL : ExplState) where
  pair : ℕ → RetainedPair sR sL
  active : ∀ i, (c.dom : Set ℂ) ⊆ H \ fillH (pair i).raw
  interval : ℕ → Set ℝ
  anchor : ℝ
  isOpen : ∀ i, IsOpen (interval i)
  isPreconnected : ∀ i, IsPreconnected (interval i)
  anchor_mem : ∀ i, anchor ∈ interval i
  landing : ∀ i x, x ∈ interval i → ∃ p : ℂ,
    (p ∈ closure (pair i).raw ∨ p.im = 0) ∧
      Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)
  base_raw : ∀ i, (pair 0).raw ⊆ (pair i).raw

/-- Supply the previously missing proper-extension field from the two
individual prefix extensions, without an additional hypothesis. -/
def RetainedIncidentGeometry.boundaryGeometry {c : Chart} {sR sL : ExplState}
    (G : RetainedIncidentGeometry c sR sL) : RetainedBoundaryGeometry c sR sL where
  pair := G.pair
  proper := fun i => hasProperBdryExt_retainedPair (G.pair i)
  active := G.active
  interval := G.interval
  anchor := G.anchor
  isOpen := G.isOpen
  isPreconnected := G.isPreconnected
  anchor_mem := G.anchor_mem
  landing := G.landing
  base_raw := G.base_raw

/-- One integer serves all retained charts and incident coordinates.
The only remaining family premise is the named physical incidence data. -/
theorem RetainedIncidentGeometry.exists_int {c : Chart} {sR sL : ExplState}
    (G : RetainedIncidentGeometry c sR sL) (hc : c.IsConformal) (hL : c.HasDerivLift) :
    ∃ n : ℤ, ∀ i x, x ∈ G.interval i →
      Tendsto (fun y => (G.pair i).chart.2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * Real.pi * n)) :=
  G.boundaryGeometry.exists_int hc hL

end InteractingSLE.Theorem14.WalkIntExtend
