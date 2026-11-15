/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInCensus

/-!
# Current shared collars from physical initial neighborhoods

PROVE-POCKET-SIDEIN. Both current domains are cut by the same ambient hull.
An outer inverse landing at a shared initial neighborhood therefore gives
a current half-disc in the transition domain. In particular, landing in
the open initial inner pocket suffices, with no surviving-coordinate input.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- Nested initial domains agree near each point inside the open inner one. -/
theorem initial_neighborhood_of_inner_mem {C U : Set ℂ} (hU : IsOpen U) (hUC : U ⊆ C)
    {p : ℂ} (hp : p ∈ U) : ∃ ε > 0, C ∩ ball p ε = U ∩ ball p ε := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU p hp
  exact ⟨ε, hε, Set.Subset.antisymm
    (fun _ hz => ⟨hball hz.2, hz.2⟩) (fun _ hz => ⟨hUC hz.1, hz.2⟩)⟩

/-- Shared initial geometry and a finite inverse landing supply the current
collar. No local survival of the initial domain is needed in this direction. -/
theorem current_collar_of_initial_neighborhood {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal) {C U F : Set ℂ} (hUC : U ⊆ C)
    (hDomO : (outer.dom : Set ℂ) = C ∩ (H \ F))
    (hDomI : (inner.dom : Set ℂ) = U ∩ (H \ F)) {p : ℂ} {ξ : ℝ}
    (hShared : ∃ ε > 0, C ∩ ball p ε = U ∩ ball p ε)
    (hLanding : Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p)) :
    ∃ r > 0, H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ) := by
  have hIncl := current_domain_inclusion_of_common_hull hUC hDomO hDomI
  obtain ⟨ε, hε, hShared⟩ := hShared
  have hEventually : ∀ᶠ z in 𝓝[H] (ξ : ℂ),
      z ∈ ((pocketTransitionChart outer inner).dom : Set ℂ) := by
    filter_upwards [self_mem_nhdsWithin,
      hLanding.eventually (ball_mem_nhds p hε)] with z hz hzball
    apply (mem_dom_pocketTransitionChart hO hI hIncl).2
    have hp : outer.2.1 z ∈ (outer.dom : Set ℂ) := hO.inv_mem_dom hz
    rw [hDomO] at hp
    have hInner : outer.2.1 z ∈ (inner.dom : Set ℂ) := by
      rw [hDomI]
      exact ⟨(hShared ▸ (show outer.2.1 z ∈ C ∩ ball p ε from ⟨hp.1, hzball⟩)).1, hp.2⟩
    exact ⟨hz, hInner⟩
  obtain ⟨r, hr, hSub⟩ := Metric.mem_nhdsWithin_iff.1 hEventually
  exact ⟨r, hr, fun _ hz => hSub ⟨hz.2, hz.1⟩⟩

/-- A finite current access landing inside the initial inner pocket has a
shared current collar, even when that access lies on the exposed hull. -/
theorem current_collar_of_landing_mem_inner {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal) {C U F : Set ℂ}
    (hU : IsOpen U) (hUC : U ⊆ C)
    (hDomO : (outer.dom : Set ℂ) = C ∩ (H \ F))
    (hDomI : (inner.dom : Set ℂ) = U ∩ (H \ F)) {p : ℂ} {ξ : ℝ}
    (hp : p ∈ U) (hLanding : Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p)) :
    ∃ r > 0, H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ) :=
  current_collar_of_initial_neighborhood hO hI hUC hDomO hDomI
    (initial_neighborhood_of_inner_mem hU hUC hp) hLanding

end InteractingSLE.Sec7.PocketStopSide
