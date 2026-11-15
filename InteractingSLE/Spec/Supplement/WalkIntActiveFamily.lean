/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntActiveWalk

/-!
# Retained reference families from prefix-before-exit geometry

The remaining family input records initial-segment inclusions and a later
common exit only for bounded components. Unbounded components need no exit
data. Active containment and joint properness are proved, then the existing
family theorem gives one integer before all indices and incident points.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntActive

open WalkMean WalkIntFill WalkIntExtend

/-- Exact remaining physical selection and incident-interval data.
Active containment and proper extension are not hypotheses. -/
structure RetainedExitGeometry (c : Chart) (sR sL : ExplState) (α β : ℝ≥0 → ℂ) where
  pair : ℕ → RetainedPair sR sL
  before : Bornology.IsBounded (c.dom : Set ℂ) →
    ∀ i, Nonempty (BeforeExit (pair i) (c.dom : Set ℂ) α β)
  interval : ℕ → Set ℝ
  anchor : ℝ
  isOpen : ∀ i, IsOpen (interval i)
  isPreconnected : ∀ i, IsPreconnected (interval i)
  anchor_mem : ∀ i, anchor ∈ interval i
  landing : ∀ i x, x ∈ interval i → ∃ p : ℂ,
    (p ∈ closure (pair i).raw ∨ p.im = 0) ∧
      Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)
  base_raw : ∀ i, (pair 0).raw ⊆ (pair i).raw

/-- Prove active containment by the unbounded-component theorem or the
contact-order continuation theorem, as appropriate. -/
def RetainedExitGeometry.incidentGeometry {c : Chart} {sR sL : ExplState}
    {α β : ℝ≥0 → ℂ} (G : RetainedExitGeometry c sR sL α β)
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {wR wL : ExplSpec} (hR : range α = physOf wR sR) (hL : range β = physOf wL sL)
    (hC : (c.dom : Set ℂ) ∈ betweenComponents (physOf wR sR) (physOf wL sL)) :
    RetainedIncidentGeometry c sR sL where
  pair := G.pair
  active := by
    intro i
    by_cases hb : Bornology.IsBounded (c.dom : Set ℂ)
    · obtain ⟨B⟩ := G.before hb i
      have hC' : (c.dom : Set ℂ) ∈ betweenComponents (range α) (range β) := by
        rw [hR, hL]
        exact hC
      exact active_retainedPair_of_beforeExit (G.pair i) hα hβ horder hC' B
    · exact active_retainedPair_of_unbounded (G.pair i) hC c.dom.isOpen hb
  interval := G.interval
  anchor := G.anchor
  isOpen := G.isOpen
  isPreconnected := G.isPreconnected
  anchor_mem := G.anchor_mem
  landing := G.landing
  base_raw := G.base_raw

/-- The common integer with active containment and joint properness
discharged. The physical selection input contains no lift comparison. -/
theorem RetainedExitGeometry.exists_int {c : Chart} {sR sL : ExplState}
    {α β : ℝ≥0 → ℂ} (G : RetainedExitGeometry c sR sL α β)
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {wR wL : ExplSpec} (hR : range α = physOf wR sR) (hL : range β = physOf wL sL)
    (hC : (c.dom : Set ℂ) ∈ betweenComponents (physOf wR sR) (physOf wL sL))
    (hc : c.IsConformal) (hLift : c.HasDerivLift) :
    ∃ n : ℤ, ∀ i x, x ∈ G.interval i →
      Tendsto (fun y => (G.pair i).chart.2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * Real.pi * n)) :=
  (G.incidentGeometry hα hβ horder hR hL hC).exists_int hc hLift

end InteractingSLE.Theorem14.WalkIntActive
