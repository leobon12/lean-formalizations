/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRetainComparison

/-!
# A shared current collar covers an initial physical neighborhood

PROVE-POCKET-SIDEIN. If the initial outer pocket remains active near an
incoming point and its current forward coordinate tends into a shared
half-disc, nesting forces the two initial pockets to agree near that point.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The shared initial neighborhood is a consequence of current collar
coverage and survival of an initial outer neighborhood. -/
theorem initial_neighborhood_of_active_collar {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hIncl : (inner.dom : Set ℂ) ⊆ outer.dom) {C U : Set ℂ} (hUC : U ⊆ C)
    (hIU : (inner.dom : Set ℂ) ⊆ U) {p : ℂ} {ξ r : ℝ} (hr : 0 < r)
    (hCollar : H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ))
    (hActive : ∀ᶠ z in 𝓝[C] p, z ∈ (outer.dom : Set ℂ))
    (hForward : Tendsto outer.1 (𝓝[C] p) (𝓝 (ξ : ℂ))) :
    ∃ ε > 0, C ∩ ball p ε = U ∩ ball p ε := by
  have hIn : ∀ᶠ z in 𝓝[C] p, z ∈ U := by
    filter_upwards [hActive, hForward.eventually (ball_mem_nhds (ξ : ℂ) hr)] with z hz hzb
    have hInner := (mem_dom_pocketTransitionChart hO hI hIncl).1
      (hCollar ⟨hO.fwd_mem hz, hzb⟩) |>.2
    rw [hO.inv_fwd hz] at hInner
    exact hIU hInner
  obtain ⟨ε, hε, hSub⟩ := Metric.mem_nhdsWithin_iff.1 hIn
  refine ⟨ε, hε, Set.Subset.antisymm ?_ ?_⟩
  · exact fun z hz => ⟨hSub ⟨hz.2, hz.1⟩, hz.2⟩
  · exact fun z hz => ⟨hUC hz.1, hz.2⟩

end InteractingSLE.Sec7.PocketStopSide
