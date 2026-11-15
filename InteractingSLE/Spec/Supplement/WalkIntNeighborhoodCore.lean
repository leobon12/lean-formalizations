/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntEnvelopeFamily
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Canonical incident intervals of a physical boundary support

Take the connected component containing the common coordinate in the
interior of the supported landing coordinates. These intervals are open,
preconnected and monotone in the physical support, without a finiteness
assumption on real contacts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex

namespace InteractingSLE.Theorem14.WalkIntNeighborhood

/-- Coordinates whose physical boundary value lies on the retained raw
closure or on the real line. -/
def landingCoordinates (c : Chart) (F : Set ℂ) : Set ℝ :=
  {x | GW4Traverse.invExt c (x : ℂ) ∈ closure F ∨
    (GW4Traverse.invExt c (x : ℂ)).im = 0}

/-- The maximal connected open incident interval containing the anchor,
when the anchor is an interior landing coordinate. -/
def incidentInterval (c : Chart) (F : Set ℂ) (anchor : ℝ) : Set ℝ :=
  connectedComponentIn (interior (landingCoordinates c F)) anchor

theorem isOpen_incidentInterval (c : Chart) (F : Set ℂ) (anchor : ℝ) :
    IsOpen (incidentInterval c F anchor) := isOpen_interior.connectedComponentIn

theorem isPreconnected_incidentInterval (c : Chart) (F : Set ℂ) (anchor : ℝ) :
    IsPreconnected (incidentInterval c F anchor) := isPreconnected_connectedComponentIn

theorem anchor_mem_incidentInterval {c : Chart} {F : Set ℂ} {anchor : ℝ}
    (ha : anchor ∈ interior (landingCoordinates c F)) :
    anchor ∈ incidentInterval c F anchor := mem_connectedComponentIn ha

theorem mem_landingCoordinates_of_mem_interval {c : Chart} {F : Set ℂ} {anchor x : ℝ}
    (hx : x ∈ incidentInterval c F anchor) : x ∈ landingCoordinates c F :=
  interior_subset (connectedComponentIn_subset _ _ hx)

/-- Increasing the retained raw support increases its landing coordinates. -/
theorem landingCoordinates_mono (c : Chart) {F G : Set ℂ} (h : F ⊆ G) :
    landingCoordinates c F ⊆ landingCoordinates c G := by
  intro x hx
  exact hx.elim (fun hF => Or.inl (closure_mono h hF)) Or.inr

/-- The canonical intervals are nested whenever the physical raw sets are. -/
theorem incidentInterval_mono (c : Chart) (anchor : ℝ) {F G : Set ℂ} (h : F ⊆ G) :
    incidentInterval c F anchor ⊆ incidentInterval c G anchor :=
  connectedComponentIn_mono anchor (interior_mono (landingCoordinates_mono c h))

end InteractingSLE.Theorem14.WalkIntNeighborhood
