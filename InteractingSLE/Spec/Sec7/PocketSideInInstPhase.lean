/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInInstCharts
import InteractingSLE.Spec.Sec7.PocketSideInInstHeight

/-!
# R.6 with the two actual current pocket means

PROVE-POCKET-SIDEIN. The exact coordinate identity is proved from the two
current charts. Equal exact shared-side limits and R.5's physical germ
comparison determine the transition phase, replacing the assumed scalar
height-transformation equation. An inner zero-phase germ then fixes the
outer exposed phase, without a restriction on the seed weights.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Sec7.PocketStopSide

/-- Physical R.5 germ preservation becomes the corrected current-coordinate
comparison for the actual transition chart and its inherited logarithm. -/
theorem tendsto_corrected_difference_of_current_germ {κ : ℝ} {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom)
    {G L : ℂ → ℂ}
    (hExtensionEq : EqOn G (pocketTransitionChart outer inner).1
      (pocketTransitionChart outer inner).dom)
    (hInheritedLog : ∀ z ∈ (pocketTransitionChart outer inner).dom,
      (L z).im = (pocketTransitionChart outer inner).2.2 z)
    {u vOuter vInner : ℂ → ℝ} {ξ r : ℝ} (hr : 0 < r)
    (hCollar : H ∩ ball (ξ : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ))
    (hPhysicalGerm : Tendsto (fun z => vInner (outer.2.1 z) - vOuter (outer.2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 0)) :
    Tendsto (fun z => sideMean κ inner u vInner (G z) - sideMean κ outer u vOuter z -
      chiC κ * (L z).im) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  refine hPhysicalGerm.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (ball_mem_nhds (ξ : ℂ) hr)] with z hzH hzball
  have hz := hCollar ⟨hzH, hzball⟩
  rw [hExtensionEq hz, hInheritedLog z hz]
  exact (sideMean_transition_sub hO hI hCurrentInclusion u vOuter vInner hz).symm

/-- Equal exact incoming heights force the transition argument to vanish.
The height-transformation equation is derived by uniqueness of the three
limits, rather than supplied as a scalar premise. -/
theorem transition_im_zero_of_current_pocket_germ {κ : ℝ} (hχ : chiC κ ≠ 0)
    {outer inner : Chart} (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom)
    {J : Set ℝ} (hJ : IsPreconnected J) {G L : ℂ → ℂ}
    (hloc : ∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G y r)
    (hLc : ContinuousOn (fun y : ℝ => L y) J)
    (hexp : ∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect G) y)
    (hExtensionEq : EqOn G (pocketTransitionChart outer inner).1
      (pocketTransitionChart outer inner).dom)
    (hInheritedLog : ∀ z ∈ (pocketTransitionChart outer inner).dom,
      (L z).im = (pocketTransitionChart outer inner).2.2 z)
    {y₀ η₀ r : ℝ} (hy₀ : y₀ ∈ J) (hr : 0 < r)
    (hCollar : H ∩ ball (y₀ : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ))
    (hL₀ : ContinuousWithinAt L Hbar (y₀ : ℂ))
    (hG₀ : Tendsto G (𝓝[H] (y₀ : ℂ)) (𝓝[H] (η₀ : ℂ)))
    {u vOuter vInner : ℂ → ℝ} {b₀ : ℝ}
    (hOuterHeight : Tendsto (sideMean κ outer u vOuter) (𝓝[H] (y₀ : ℂ)) (𝓝 b₀))
    (hInnerHeight : Tendsto (sideMean κ inner u vInner) (𝓝[H] (η₀ : ℂ)) (𝓝 b₀))
    (hPhysicalGerm : Tendsto (fun z => vInner (outer.2.1 z) - vOuter (outer.2.1 z))
      (𝓝[H] (y₀ : ℂ)) (𝓝 0)) : ∀ y ∈ J, (L y).im = 0 := by
  have hcompare := tendsto_corrected_difference_of_current_germ (κ := κ) (u := u)
    hO hI hCurrentInclusion
    hExtensionEq hInheritedLog hr hCollar hPhysicalGerm
  have harg := ((Complex.continuous_im.tendsto (L y₀)).comp
    (hL₀.mono QuantumZipper.H_subset_Hbar).tendsto).const_mul (chiC κ)
  have : NeBot (𝓝[H] (y₀ : ℂ)) := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  have he := tendsto_nhds_unique (((hInnerHeight.comp hG₀).sub hOuterHeight).sub harg) hcompare
  have htransform : b₀ = b₀ + chiC κ * (L y₀).im := by linarith only [he]
  exact transition_im_zero_of_shared_height hχ hJ hloc hLc hexp hy₀ rfl htransform

/-- The actual two current means, their common incoming exact height, and
the two physical R.5 germs transfer a canonical inner exposed height to the
outer pocket. Neither coordinate increment nor scalar height transformation
is a premise. All seed weights are permitted by this deterministic step. -/
theorem phase_eq_zero_of_shared_current_pocket_germs {κ : ℝ} (hχ : chiC κ ≠ 0)
    {outer inner : Chart} (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom)
    {J : Set ℝ} (hJ : IsPreconnected J) {G L : ℂ → ℂ}
    (hloc : ∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G y r)
    (hLc : ContinuousOn (fun y : ℝ => L y) J)
    (hexp : ∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect G) y)
    (hExtensionEq : EqOn G (pocketTransitionChart outer inner).1
      (pocketTransitionChart outer inner).dom)
    (hInheritedLog : ∀ z ∈ (pocketTransitionChart outer inner).dom,
      (L z).im = (pocketTransitionChart outer inner).2.2 z)
    {y₀ η₀ r₀ : ℝ} (hy₀ : y₀ ∈ J) (hr₀ : 0 < r₀)
    (hCollar₀ : H ∩ ball (y₀ : ℂ) r₀ ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ))
    (hL₀ : ContinuousWithinAt L Hbar (y₀ : ℂ))
    (hG₀ : Tendsto G (𝓝[H] (y₀ : ℂ)) (𝓝[H] (η₀ : ℂ)))
    {u vOuter vInner : ℂ → ℝ} {b₀ : ℝ}
    (hOuterHeight : Tendsto (sideMean κ outer u vOuter) (𝓝[H] (y₀ : ℂ)) (𝓝 b₀))
    (hInnerHeight : Tendsto (sideMean κ inner u vInner) (𝓝[H] (η₀ : ℂ)) (𝓝 b₀))
    (hPhysicalGerm₀ : Tendsto (fun z => vInner (outer.2.1 z) - vOuter (outer.2.1 z))
      (𝓝[H] (y₀ : ℂ)) (𝓝 0))
    {ξ η r : ℝ} (hξ : ξ ∈ J) (hr : 0 < r)
    (hCollar : H ∩ ball (ξ : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ))
    (hLξ : ContinuousWithinAt L Hbar (ξ : ℂ))
    (hGξ : Tendsto G (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ))) {b d : ℝ}
    (hOuterExposed : Tendsto (sideMean κ outer u vOuter) (𝓝[H] (ξ : ℂ)) (𝓝 (b + d)))
    (hInnerExposed : Tendsto (sideMean κ inner u vInner) (𝓝[H] (η : ℂ)) (𝓝 b))
    (hPhysicalGerm : Tendsto (fun z => vInner (outer.2.1 z) - vOuter (outer.2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 0)) : d = 0 := by
  have hzero := transition_im_zero_of_current_pocket_germ hχ hO hI hCurrentInclusion hJ
    hloc hLc hexp hExtensionEq hInheritedLog hy₀ hr₀ hCollar₀ hL₀ hG₀
    hOuterHeight hInnerHeight hPhysicalGerm₀
  have htransform : b₀ = b₀ + chiC κ * (L y₀).im := by rw [hzero y₀ hy₀]; ring
  exact phase_eq_zero_of_inner_germ hχ hJ hloc hLc hexp hy₀ rfl htransform hξ hLξ hGξ
    hOuterExposed hInnerExposed
    (tendsto_corrected_difference_of_current_germ hO hI hCurrentInclusion
      hExtensionEq hInheritedLog hr hCollar hPhysicalGerm)

end InteractingSLE.Sec7.PocketStopSide
