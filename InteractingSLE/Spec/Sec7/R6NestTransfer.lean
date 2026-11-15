/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInInstPhase
import InteractingSLE.Spec.Sec7.PocketStopSideLimPhase

/-!
# Lemma R.6 with independent offsets: the two exposed phases are equal

PROVE-R6-NESTED. Lemma R.6 (supplement p. 476; Astra's follow-up 5, Lemma 3.1, R73) in the form needed by the
phase words of `PocketStopSide.PocketStopPhaseSideLimit`: each pocket's word is read up to its **own** additive
offset (`a` in `PocketStopPhaseSideLimit`, which also absorbs the integer branch of the chart's lift), so the two
charts need not give the shared unvisited side the same numerical height. If the two words give the shared side
the same canonical height `b₀` up to their offsets, and the two exposed points the same canonical height `b` up to
the offsets and phases `d_O`, `d_I`, then the reflection across the connected interval `J` and the two R.5 physical
germ comparisons force `d_O = d_I`: the transition argument is one constant on `J`, which the shared side identifies
with the offset difference, and which the exposed side then transfers. No bound on the seed weights and no
condition `χ ≠ 0` are used. This generalizes `PocketStopSide.phase_eq_zero_of_shared_current_pocket_germs` (equal
offsets, inner phase `0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Sec7.R6Nest

open PocketStopSide

/-- The transition argument is one constant along a connected interval across which the transition reflects with
positive derivative (R16's lattice argument). -/
theorem transition_im_eq {J : Set ℝ} (hJ : IsPreconnected J) {G L : ℂ → ℂ}
    (hloc : ∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G y r)
    (hLc : ContinuousOn (fun y : ℝ => L y) J)
    (hexp : ∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect G) y)
    {y₁ y₂ : ℝ} (h₁ : y₁ ∈ J) (h₂ : y₂ ∈ J) : (L y₁).im = (L y₂).im := by
  have hpos : ∀ y ∈ J, 0 < (Complex.exp ((fun y : ℝ => L y) y)).re ∧
      (Complex.exp ((fun y : ℝ => L y) y)).im = 0 := by
    intro y hy
    obtain ⟨r, hr, hφ⟩ := hloc y hy
    obtain ⟨hi, hre⟩ := hφ.deriv_schwarzReflect_pos (mem_ball_self hr)
    rw [hexp y hy]
    exact ⟨hre, hi⟩
  exact R16.im_eq_of_exp_pos hJ hLc hpos h₁ h₂

/-- **Lemma R.6 with independent offsets.** Two current pocket charts with nested current domains, a connected
real interval `J` across which their transition reflects with positive derivative, the inherited transition
logarithm, collars at a shared-side point `y₀ ∈ J` and an exposed point `ξ ∈ J`, and the two R.5 physical germ
comparisons. If the outer and inner corrected means have limits `b₀ − a_O`, `b₀ − a_I` at the shared side and
`b + d_O − a_O`, `b + d_I − a_I` at the exposed points, then `d_O = d_I`. -/
theorem phase_eq_of_shared_current_pocket_germs {κ : ℝ} {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
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
    {u vOuter vInner : ℂ → ℝ} {b₀ aO aI : ℝ}
    (hOuterHeight : Tendsto (sideMean κ outer u vOuter) (𝓝[H] (y₀ : ℂ)) (𝓝 (b₀ - aO)))
    (hInnerHeight : Tendsto (sideMean κ inner u vInner) (𝓝[H] (η₀ : ℂ)) (𝓝 (b₀ - aI)))
    (hPhysicalGerm₀ : Tendsto (fun z => vInner (outer.2.1 z) - vOuter (outer.2.1 z))
      (𝓝[H] (y₀ : ℂ)) (𝓝 0))
    {ξ η r : ℝ} (hξ : ξ ∈ J) (hr : 0 < r)
    (hCollar : H ∩ ball (ξ : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ))
    (hLξ : ContinuousWithinAt L Hbar (ξ : ℂ))
    (hGξ : Tendsto G (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ))) {b dO dI : ℝ}
    (hOuterExposed : Tendsto (sideMean κ outer u vOuter) (𝓝[H] (ξ : ℂ)) (𝓝 (b + dO - aO)))
    (hInnerExposed : Tendsto (sideMean κ inner u vInner) (𝓝[H] (η : ℂ)) (𝓝 (b + dI - aI)))
    (hPhysicalGerm : Tendsto (fun z => vInner (outer.2.1 z) - vOuter (outer.2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 0)) : dO = dI := by
  have hneBot : ∀ x : ℝ, NeBot (𝓝[H] (x : ℂ)) := fun x => mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp only [Complex.ofReal_im]))
  have harg : ∀ x : ℝ, ContinuousWithinAt L Hbar (x : ℂ) →
      Tendsto (fun z => chiC κ * (L z).im) (𝓝[H] (x : ℂ)) (𝓝 (chiC κ * (L x).im)) := fun x hx =>
    ((Complex.continuous_im.tendsto (L x)).comp (hx.mono QuantumZipper.H_subset_Hbar).tendsto).const_mul _
  have h₀ := tendsto_corrected_difference_of_current_germ (κ := κ) (u := u) hO hI hCurrentInclusion
    hExtensionEq hInheritedLog hr₀ hCollar₀ hPhysicalGerm₀
  have h₁ := tendsto_corrected_difference_of_current_germ (κ := κ) (u := u) hO hI hCurrentInclusion
    hExtensionEq hInheritedLog hr hCollar hPhysicalGerm
  have := hneBot y₀
  have e₀ := tendsto_nhds_unique (((hInnerHeight.comp hG₀).sub hOuterHeight).sub (harg y₀ hL₀)) h₀
  have := hneBot ξ
  have e₁ := tendsto_nhds_unique (((hInnerExposed.comp hGξ).sub hOuterExposed).sub (harg ξ hLξ)) h₁
  have hc := transition_im_eq hJ hloc hLc hexp hξ hy₀
  rw [hc] at e₁
  linarith only [e₀, e₁]

/-- **Lemma R.6 for two phase words** (the form of `PocketStopSide.PocketStopPhaseSideLimit`): if each chart's
corrected mean has the limit `phaseData … d − a` of its own word (own weights, marks, phase and offset) at a point
`y₀`/`η₀` of the shared unvisited side (outside the exposed intervals) and at exposed points `ξ`/`η` (inside them),
and the two words give the shared-side points and the exposed points the same canonical heights, then the two phases
agree. -/
theorem phase_eq_of_shared_current_pocket_words {κ : ℝ} {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom)
    {J : Set ℝ} (hJ : IsPreconnected J) {G L : ℂ → ℂ}
    (hloc : ∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G y r)
    (hLc : ContinuousOn (fun y : ℝ => L y) J)
    (hexp : ∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect G) y)
    (hExtensionEq : EqOn G (pocketTransitionChart outer inner).1
      (pocketTransitionChart outer inner).dom)
    (hInheritedLog : ∀ z ∈ (pocketTransitionChart outer inner).dom,
      (L z).im = (pocketTransitionChart outer inner).2.2 z)
    {nL nR mL mR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {vL : Fin (nL + 1) → ℝ}
    {vR : Fin (nR + 1) → ℝ} {σL : Fin (mL + 1) → ℝ} {σR : Fin (mR + 1) → ℝ} {wL : Fin (mL + 1) → ℝ}
    {wR : Fin (mR + 1) → ℝ}
    {y₀ η₀ r₀ : ℝ} (hy₀ : y₀ ∈ J) (hr₀ : 0 < r₀)
    (hCollar₀ : H ∩ ball (y₀ : ℂ) r₀ ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ))
    (hL₀ : ContinuousWithinAt L Hbar (y₀ : ℂ))
    (hG₀ : Tendsto G (𝓝[H] (y₀ : ℂ)) (𝓝[H] (η₀ : ℂ)))
    {u vOuter vInner : ℂ → ℝ} {aO aI dO dI : ℝ}
    (hy₀Out : y₀ ∉ Ioo (vL 0) (vR 0)) (hη₀Out : η₀ ∉ Ioo (wL 0) (wR 0))
    (hSharedHeight : forceBoundaryData κ ρL ρR vL vR y₀ = forceBoundaryData κ σL σR wL wR η₀)
    (hOuterHeight : Tendsto (sideMean κ outer u vOuter) (𝓝[H] (y₀ : ℂ))
      (𝓝 (PhaseSel.phaseData κ ρL ρR vL vR dO y₀ - aO)))
    (hInnerHeight : Tendsto (sideMean κ inner u vInner) (𝓝[H] (η₀ : ℂ))
      (𝓝 (PhaseSel.phaseData κ σL σR wL wR dI η₀ - aI)))
    (hPhysicalGerm₀ : Tendsto (fun z => vInner (outer.2.1 z) - vOuter (outer.2.1 z))
      (𝓝[H] (y₀ : ℂ)) (𝓝 0))
    {ξ η r : ℝ} (hξ : ξ ∈ J) (hr : 0 < r)
    (hCollar : H ∩ ball (ξ : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ))
    (hLξ : ContinuousWithinAt L Hbar (ξ : ℂ))
    (hGξ : Tendsto G (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ)))
    (hξIn : ξ ∈ Ioo (vL 0) (vR 0)) (hηIn : η ∈ Ioo (wL 0) (wR 0))
    (hExposedHeight : forceBoundaryData κ ρL ρR vL vR ξ = forceBoundaryData κ σL σR wL wR η)
    (hOuterExposed : Tendsto (sideMean κ outer u vOuter) (𝓝[H] (ξ : ℂ))
      (𝓝 (PhaseSel.phaseData κ ρL ρR vL vR dO ξ - aO)))
    (hInnerExposed : Tendsto (sideMean κ inner u vInner) (𝓝[H] (η : ℂ))
      (𝓝 (PhaseSel.phaseData κ σL σR wL wR dI η - aI)))
    (hPhysicalGerm : Tendsto (fun z => vInner (outer.2.1 z) - vOuter (outer.2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 0)) : dO = dI := by
  simp only [PhaseSel.phaseData, indicator_of_notMem hy₀Out, indicator_of_notMem hη₀Out,
    indicator_of_mem hξIn, indicator_of_mem hηIn, Pi.one_apply, mul_zero, mul_one, add_zero]
    at hOuterHeight hInnerHeight hOuterExposed hInnerExposed
  rw [hSharedHeight] at hOuterHeight
  rw [hExposedHeight] at hOuterExposed
  exact phase_eq_of_shared_current_pocket_germs hO hI hCurrentInclusion hJ hloc hLc hexp hExtensionEq
    hInheritedLog hy₀ hr₀ hCollar₀ hL₀ hG₀ hOuterHeight hInnerHeight hPhysicalGerm₀ hξ hr hCollar hLξ hGξ
    hOuterExposed hInnerExposed hPhysicalGerm

end InteractingSLE.Sec7.R6Nest
