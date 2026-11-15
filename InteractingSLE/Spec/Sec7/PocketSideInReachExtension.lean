/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInReachLimit

/-!
# Constructing a transition extension without a global gate boundary

PROVE-POCKET-SIDEIN. The existing inner inverse extension and local bounds
construct real limits of the transition on every shared collar. Extending
by these limits gives continuity and positive reflection on the whole
open real interval. A GB11 gate-boundary object is unnecessary for this step.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.PocketStopSide

/-- Construct the finite transition extension directly from the inner
inverse, the physical outer limits, and shared locally bounded collars. -/
theorem exists_transition_extension_of_inverse_and_bounds {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hIncl : (inner.dom : Set ℂ) ⊆ outer.dom) {E : ℂ → ℂ}
    (hE : EqOn E inner.2.1 H) (hEc : ContinuousOn E Hbar)
    {J : Set ℝ} (hJo : IsOpen J)
    (hCollars : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ))
    {p : ℝ → ℂ} (hLanding : ∀ x ∈ J,
      Tendsto outer.2.1 (𝓝[H] (x : ℂ)) (𝓝 (p x)))
    (hBound : ∀ x ∈ J, ∃ M : ℝ, ∀ᶠ z in
      𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart outer inner).1 z‖ ≤ M) :
    ∃ G : ℂ → ℂ,
      EqOn G (pocketTransitionChart outer inner).1 (pocketTransitionChart outer inner).dom ∧
      ContinuousOn G (((pocketTransitionChart outer inner).dom : Set ℂ) ∪ Complex.ofReal '' J) ∧
      (∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r) ∧
      (∀ x ∈ J, E (G x) = p x) := by
  have hc := isConformal_pocketTransitionChart hO hI hIncl
  have hcl : ∀ x ∈ J, (x : ℂ) ∈ closure ((pocketTransitionChart outer inner).dom : Set ℂ) := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := hCollars x hx
    have hxH : (x : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact mem_Hbar_of_im_eq_zero (by simp)
    exact closure_mono hsub (isOpen_ball.closure_inter ⟨hxH, mem_ball_self hr⟩)
  have hlim : ∀ x ∈ J, ∃ y : ℝ, E y = p x ∧
      Tendsto (pocketTransitionChart outer inner).1
        (𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (x : ℂ)) (𝓝 (y : ℂ)) := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := hCollars x hx
    obtain ⟨y, hy, hT⟩ := exists_real_transition_limit_of_local_bound
      hO hI hIncl hE hEc hr hsub (hLanding x hx) (hBound x hx)
    exact ⟨y, hy, hT.mono_left (nhdsWithin_mono _ hc.dom_subset)⟩
  let G := extendFrom ((pocketTransitionChart outer inner).dom : Set ℂ)
    (pocketTransitionChart outer inner).1
  have hGeq : EqOn G (pocketTransitionChart outer inner).1
      (pocketTransitionChart outer inner).dom := extendFrom_extends hc.differentiableOn_fwd.continuousOn
  have hGc : ContinuousOn G
      (((pocketTransitionChart outer inner).dom : Set ℂ) ∪ Complex.ofReal '' J) := by
    apply continuousOn_extendFrom
    · rintro z (hz | ⟨x, hx, rfl⟩)
      · exact subset_closure hz
      · exact hcl x hx
    · rintro z (hz | ⟨x, hx, rfl⟩)
      · exact ⟨_, hc.differentiableOn_fwd.continuousOn z hz⟩
      · obtain ⟨y, -, hy⟩ := hlim x hx
        exact ⟨_, hy⟩
  refine ⟨G, hGeq, hGc,
    realBoundaryConformal_of_shared_face hc hJo hCollars hGc hGeq, ?_⟩
  intro x hx
  obtain ⟨y, hy, hT⟩ := hlim x hx
  change E (extendFrom _ _ (x : ℂ)) = _
  rw [extendFrom_eq (hcl x hx) hT, hy]

end InteractingSLE.Sec7.PocketStopSide
