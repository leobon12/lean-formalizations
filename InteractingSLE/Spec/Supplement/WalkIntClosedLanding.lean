/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntClosedActive
import InteractingSLE.Spec.Supplement.WalkIntNeighborhoodBoundary

/-!
# Completed prefixes feed the existing common-integer theorem

Use the existing canonical incident intervals and LandingHullFamily.
Properness of the joint charts is already proved for closed-time pairs.
Physical active containment and one interior anchor supply its remaining
geometric fields. No new derivative-lift argument is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntClosed

open WalkIntNeighborhood

/-- Canonical incident intervals turn closed-time pairs into the existing
physical landing family used by the one-common-integer theorem. -/
def closedLandingFamily {c : Chart} {sR sL : ExplState}
    (pair : ℕ → ClosedPair sR sL) (anchor : ℝ) {R L C : Set ℂ}
    (hchart : IsComponentChart R L C c) (hCo : IsOpen C)
    (hbase : ∀ i, (pair 0).raw ⊆ (pair i).raw)
    (hActive : ∀ i, (c.dom : Set ℂ) ⊆ H \ fillH (pair i).raw)
    (hEntry : anchor ∈ interior (landingCoordinates c (pair 0).raw)) :
    WalkIntFiber.LandingHullFamily c where
  chart := fun i => (pair i).chart
  normalized := fun i => (pair i).normalized
  proper := fun i => (pair i).hasProperBdryExt
  model := fun i => (pair i).model
  interval := fun i => incidentInterval c (pair i).raw anchor
  anchor := anchor
  dom_subset := by
    intro i z hz
    rw [(pair i).model.dom_eq, (pair i).filled]
    exact hActive i hz
  isOpen := fun i => isOpen_incidentInterval c (pair i).raw anchor
  isPreconnected := fun i => isPreconnected_incidentInterval c (pair i).raw anchor
  anchor_mem := fun i => anchor_mem_incidentInterval
    (interior_mono (landingCoordinates_mono c (hbase i)) hEntry)
  landing := by
    intro i x hx
    obtain ⟨p, hp, hlim⟩ := landing_of_mem_interval hchart hCo hx
    refine ⟨p, ?_, hlim⟩
    intro hpd
    have hH := (pair i).normalized.conformal.dom_subset hpd
    rcases hp with hp | hp
    · have hpf := mem_fillH_of_mem_closure hH hp
      change p ∈ ((pair i).chart.dom : Set ℂ) at hpd
      rw [(pair i).model.dom_eq, (pair i).filled] at hpd
      exact hpd.2 hpf
    · exact (ne_of_gt (show 0 < p.im from hH)) hp
  base_subset := by
    intro i
    rw [(pair 0).filled, (pair i).filled]
    exact fillH_mono (hbase i)

/-- The inherited analytic theorem supplies one integer for every closed
reference and every coordinate in its canonical incident interval. -/
theorem exists_int_of_closed_landing {c : Chart} {sR sL : ExplState}
    (pair : ℕ → ClosedPair sR sL) (anchor : ℝ) {R L C : Set ℂ}
    (hchart : IsComponentChart R L C c) (hCo : IsOpen C)
    (hbase : ∀ i, (pair 0).raw ⊆ (pair i).raw)
    (hActive : ∀ i, (c.dom : Set ℂ) ⊆ H \ fillH (pair i).raw)
    (hEntry : anchor ∈ interior (landingCoordinates c (pair 0).raw))
    (hc : c.IsConformal) (hLift : c.HasDerivLift) :
    ∃ n : ℤ, ∀ i x, x ∈ incidentInterval c (pair i).raw anchor →
      Tendsto (fun y => (pair i).chart.2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * Real.pi * n)) :=
  (closedLandingFamily pair anchor hchart hCo hbase hActive hEntry).exists_int hc hLift

end InteractingSLE.Theorem14.WalkIntClosed
