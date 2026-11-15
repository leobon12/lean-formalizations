/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRealContacts

/-!
# Shared collars from the constructed current contacts

PROVE-POCKET-SIDEIN. The current-component identity is proved using the
constructed contact set. Real contact avoidance and one access then give
the actual shared interval. No arbitrary contact-set coverage is assumed.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The relative domain is the component selected by its constructed
current contacts, at every point of that domain. -/
theorem current_face_eq_component_of_current_contacts {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom) {p : ℂ}
    (hp : p ∈ (pocketTransitionChart outer inner).dom) :
    ((pocketTransitionChart outer inner).dom : Set ℂ) =
      connectedComponentIn (H \ currentPocketContacts outer inner) p :=
  current_face_eq_component_of_frontier
    (isConformal_pocketTransitionChart hO hI hCurrentInclusion)
    (disjoint_currentPocketContacts hO hI hCurrentInclusion)
    (frontier_subset_currentPocketContacts hO hI hCurrentInclusion) hp

/-- A connected real interval avoiding the actual current contacts and
one boundary access supply all shared half-disc collars. -/
theorem shared_collars_of_current_contacts {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom)
    {J : Set ℝ} (hJ : IsPreconnected J)
    (hContact : ∀ x ∈ J, (x : ℂ) ∉ currentPocketContacts outer inner)
    {y₀ : ℝ} (hy₀ : y₀ ∈ J)
    (hAccess : (y₀ : ℂ) ∈ closure ((pocketTransitionChart outer inner).dom : Set ℂ)) :
    ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ) := by
  have hc := isConformal_pocketTransitionChart hO hI hCurrentInclusion
  have hp : (pocketTransitionChart outer inner).2.1 I ∈
      (pocketTransitionChart outer inner).dom := hc.inv_mem_dom (by simp [H])
  have heq := current_face_eq_component_of_current_contacts hO hI hCurrentInclusion hp
  rw [heq] at hAccess ⊢
  exact exists_halfDisc_in_component_of_real_interval
    (isClosed_currentPocketContacts outer inner) hJ hContact hy₀ hAccess

/-- Astra's mixed-pocket real contact bounds yield the shared interval
using the actual constructed contacts; closedness and frontier identities
are no longer independent geometric inputs. -/
theorem shared_interval_of_current_contact_order {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom)
    {VL qβ W pU y₀ : ℝ} (hVL : VL ≤ qβ) (hqW : qβ < W) (hWp : W < pU)
    (hContactOrder : ∀ x : ℝ, (x : ℂ) ∈ currentPocketContacts outer inner →
      x ≤ VL ∨ x = qβ ∨ pU ≤ x)
    (hy₀ : y₀ ∈ Ioo qβ pU)
    (hAccess : (y₀ : ℂ) ∈ closure ((pocketTransitionChart outer inner).dom : Set ℂ)) :
    W ∈ Ioo qβ pU ∧ ∀ x ∈ Ioo qβ pU, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ) := by
  refine ⟨⟨hqW, hWp⟩, shared_collars_of_current_contacts hO hI hCurrentInclusion
    isPreconnected_Ioo (fun x hx hxc => ?_) hy₀ hAccess⟩
  rcases hContactOrder x hxc with h | h | h
  · exact (not_le_of_gt hx.1) (h.trans hVL)
  · exact (ne_of_gt hx.1) h
  · exact (not_le_of_gt hx.2) h

end InteractingSLE.Sec7.PocketStopSide
