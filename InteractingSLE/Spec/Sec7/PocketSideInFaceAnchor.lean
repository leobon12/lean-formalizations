/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInFaceReflect

/-!
# R.6: the phase anchor from current-face geometry

PROVE-POCKET-SIDEIN. The current face is identified with its actual complement
component. Contact avoidance and one shared-side access supply all local
collars, and a chart extension supplies reflection. Exact inherited heights
then anchor the transition logarithm, including for larger seed weights.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The current-face condition produces R16's reflection input. The component
identity, real contact avoidance, and shared-side access are the exact
geometric inputs still to be checked for a chosen pair of actual pockets. -/
theorem realBoundaryConformal_of_current_face {c : Chart} (hc : c.IsConformal)
    {Γ : Set ℂ} (hΓ : IsClosed Γ) {p : ℂ}
    (hCurrentFace : (c.dom : Set ℂ) = connectedComponentIn (H \ Γ) p)
    {J : Set ℝ} (hJ : IsPreconnected J) (hJo : IsOpen J)
    (hContact : ∀ x ∈ J, (x : ℂ) ∉ Γ) {y₀ : ℝ} (hy₀ : y₀ ∈ J)
    (hAccess : (y₀ : ℂ) ∈ closure (c.dom : Set ℂ)) {G : ℂ → ℂ}
    (hBoundaryExtension : ContinuousOn G ((c.dom : Set ℂ) ∪ Complex.ofReal '' J))
    (hExtensionEq : EqOn G c.1 c.dom) :
    ∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r := by
  apply realBoundaryConformal_of_shared_face hc hJo _ hBoundaryExtension hExtensionEq
  rw [hCurrentFace] at hAccess ⊢
  exact exists_halfDisc_in_component_of_real_interval hΓ hJ hContact hy₀ hAccess

/-- Current-face geometry and equal exact shared-side heights fix the
transition phase on the whole interval, with no restriction on seed weights. -/
theorem transition_im_zero_of_current_face {χ : ℝ} (hχ : χ ≠ 0)
    {c : Chart} (hc : c.IsConformal) {Γ : Set ℂ} (hΓ : IsClosed Γ) {p : ℂ}
    (hCurrentFace : (c.dom : Set ℂ) = connectedComponentIn (H \ Γ) p)
    {J : Set ℝ} (hJ : IsPreconnected J) (hJo : IsOpen J)
    (hContact : ∀ x ∈ J, (x : ℂ) ∉ Γ) {y₀ : ℝ} (hy₀ : y₀ ∈ J)
    (hAccess : (y₀ : ℂ) ∈ closure (c.dom : Set ℂ)) {G L : ℂ → ℂ}
    (hBoundaryExtension : ContinuousOn G ((c.dom : Set ℂ) ∪ Complex.ofReal '' J))
    (hExtensionEq : EqOn G c.1 c.dom)
    (hLc : ContinuousOn (fun y : ℝ => L y) J)
    (hexp : ∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect G) y)
    {bC bU : ℝ} (hExactHeights : bC = bU)
    (hHeightTransform : bU = bC + χ * (L y₀).im) :
    ∀ y ∈ J, (L y).im = 0 :=
  transition_im_zero_of_shared_height hχ hJ
    (realBoundaryConformal_of_current_face hc hΓ hCurrentFace hJ hJo hContact hy₀
      hAccess hBoundaryExtension hExtensionEq)
    hLc hexp hy₀ hExactHeights hHeightTransform

/-- The shared-face construction discharges the local reflection premises of
the inner-to-outer exposed phase transfer. Only a local mean germ comparison
is used; whole conditional means are not identified. -/
theorem phase_eq_zero_of_current_face_germ {χ : ℝ} (hχ : χ ≠ 0)
    {c : Chart} (hc : c.IsConformal) {Γ : Set ℂ} (hΓ : IsClosed Γ) {p : ℂ}
    (hCurrentFace : (c.dom : Set ℂ) = connectedComponentIn (H \ Γ) p)
    {J : Set ℝ} (hJ : IsPreconnected J) (hJo : IsOpen J)
    (hContact : ∀ x ∈ J, (x : ℂ) ∉ Γ) {y₀ : ℝ} (hy₀ : y₀ ∈ J)
    (hAccess : (y₀ : ℂ) ∈ closure (c.dom : Set ℂ)) {G L : ℂ → ℂ}
    (hBoundaryExtension : ContinuousOn G ((c.dom : Set ℂ) ∪ Complex.ofReal '' J))
    (hExtensionEq : EqOn G c.1 c.dom)
    (hLc : ContinuousOn (fun y : ℝ => L y) J)
    (hexp : ∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect G) y)
    {bC bU : ℝ} (hExactHeights : bC = bU)
    (hHeightTransform : bU = bC + χ * (L y₀).im)
    {ξ η : ℝ} (hξ : ξ ∈ J) (hLξ : ContinuousWithinAt L Hbar (ξ : ℂ))
    (hG : Tendsto G (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ)))
    {MC MU : ℂ → ℝ} {b d : ℝ}
    (hC : Tendsto MC (𝓝[H] (ξ : ℂ)) (𝓝 (b + d)))
    (hU : Tendsto MU (𝓝[H] (η : ℂ)) (𝓝 b))
    (hGermComparison : Tendsto (fun z => MU (G z) - MC z - χ * (L z).im)
      (𝓝[H] (ξ : ℂ)) (𝓝 0)) : d = 0 :=
  phase_eq_zero_of_inner_germ hχ hJ
    (realBoundaryConformal_of_current_face hc hΓ hCurrentFace hJ hJo hContact hy₀
      hAccess hBoundaryExtension hExtensionEq)
    hLc hexp hy₀ hExactHeights hHeightTransform hξ hLξ hG hC hU hGermComparison

end InteractingSLE.Sec7.PocketStopSide
