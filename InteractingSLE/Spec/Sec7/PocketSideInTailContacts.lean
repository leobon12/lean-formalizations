/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInTailAccess
import InteractingSLE.Spec.Sec7.PocketSideInRealContacts

/-!
# A surviving old collar excludes the actual current contacts

PROVE-POCKET-SIDEIN. The old-coordinate half-disc is in the relative
current domain. Its whole open ball therefore avoids the closure of the
interior relative frontier, which is the constructed current contact set.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- An unfilled relative half-disc excludes all constructed current
contacts in the corresponding ball, including their closure on the real line. -/
theorem disjoint_currentPocketContacts_of_halfDisc {old current : Chart}
    (hOld : old.IsConformal) (hCurrent : current.IsConformal)
    (hInclusion : (current.dom : Set ℂ) ⊆ old.dom) {x d : ℝ}
    (hCollar : H ∩ ball (x : ℂ) d ⊆
      ((pocketTransitionChart old current).dom : Set ℂ)) :
    Disjoint (ball (x : ℂ) d) (currentPocketContacts old current) := by
  rw [currentPocketContacts_eq hOld hCurrent hInclusion]
  refine Disjoint.closure_right (disjoint_left.2 ?_) isOpen_ball
  intro z hzball hzfrontier
  have hz := hCollar ⟨hzfrontier.2, hzball⟩
  rw [(pocketTransitionChart old current).dom.isOpen.frontier_eq] at hzfrontier
  exact hzfrontier.1.2 hz

/-- A physical old-inverse collar in the current domain is also a
half-disc in the relative chart domain. -/
theorem halfDisc_subset_transition_of_inverse_image {old current : Chart}
    (hOld : old.IsConformal) (hCurrent : current.IsConformal)
    (hInclusion : (current.dom : Set ℂ) ⊆ old.dom) {x d : ℝ}
    (hCollar : old.2.1 '' (H ∩ ball (x : ℂ) d) ⊆ (current.dom : Set ℂ)) :
    H ∩ ball (x : ℂ) d ⊆ ((pocketTransitionChart old current).dom : Set ℂ) := by
  intro z hz
  exact (mem_dom_pocketTransitionChart hOld hCurrent hInclusion).2
    ⟨hz.1, hCollar (mem_image_of_mem old.2.1 hz)⟩

end InteractingSLE.Sec7.PocketStopSide
