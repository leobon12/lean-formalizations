/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideLimPhase
import InteractingSLE.Spec.Supplement.R6RefPhase

/-!
# R.6 at the side-limit level

PROVE-STRIPSYS38. A shared unvisited side with equal exact heights fixes the
transition logarithm at zero. R16's reflection theorem propagates that value
along the shared interval. Comparing one exposed germ with an inner canonical
germ then determines the common exposed phase, without a bound on seed weights.
Only the germ difference is compared; no equality of complete conditional means
or conditioning on unrevealed inner labels is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The coordinate mean in one current chart, before the common field offset. -/
def sideMean (κ : ℝ) (c : Chart) (u v : ℂ → ℝ) (z : ℂ) : ℝ :=
  v (c.2.1 z) + u (c.2.1 z) + chiC κ * c.2.2 (c.2.1 z)

/-- Equal exact heights on the shared unvisited side fix the inherited
transition argument on the whole connected interval, by R.6. -/
theorem transition_im_zero_of_shared_height {χ : ℝ} (hχ : χ ≠ 0)
    {J : Set ℝ} (hJ : IsPreconnected J) {φ L : ℂ → ℂ}
    (hloc : ∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal φ y r)
    (hLc : ContinuousOn (fun y : ℝ => L y) J)
    (hexp : ∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect φ) y)
    {y₀ : ℝ} (hy₀ : y₀ ∈ J) {bC bU : ℝ} (hsame : bC = bU)
    (htransform : bU = bC + χ * (L y₀).im) : ∀ y ∈ J, (L y).im = 0 := by
  have hprod : χ * (L y₀).im = 0 := by linarith only [hsame, htransform]
  exact (R16.r6_phase_const hJ hloc hLc hexp).2 y₀ hy₀ ((mul_eq_zero.1 hprod).resolve_left hχ)

/-- A zero-phase inner exposed germ determines the common outer phase at this
visit. The transition is anchored by an unvisited side, and only a vanishing
germ difference between the two coordinate means is assumed. -/
theorem phase_eq_zero_of_inner_germ {χ : ℝ} (hχ : χ ≠ 0)
    {J : Set ℝ} (hJ : IsPreconnected J) {φ L : ℂ → ℂ}
    (hloc : ∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal φ y r)
    (hLc : ContinuousOn (fun y : ℝ => L y) J)
    (hexp : ∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect φ) y)
    {y₀ : ℝ} (hy₀ : y₀ ∈ J) {bC bU : ℝ} (hsame : bC = bU)
    (htransform : bU = bC + χ * (L y₀).im)
    {ξ η : ℝ} (hξ : ξ ∈ J) (hLξ : ContinuousWithinAt L Hbar (ξ : ℂ))
    (hφ : Tendsto φ (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ)))
    {MC MU : ℂ → ℝ} {b d : ℝ}
    (hC : Tendsto MC (𝓝[H] (ξ : ℂ)) (𝓝 (b + d)))
    (hU : Tendsto MU (𝓝[H] (η : ℂ)) (𝓝 b))
    (hStoppedGermComparison : Tendsto (fun z => MU (φ z) - MC z - χ * (L z).im)
      (𝓝[H] (ξ : ℂ)) (𝓝 0)) : d = 0 := by
  have hzero := transition_im_zero_of_shared_height hχ hJ hloc hLc hexp hy₀ hsame htransform
  have hLlim : Tendsto (fun z => (L z).im) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
    have h := (Complex.continuous_im.tendsto (L ξ)).comp
      (hLξ.mono QuantumZipper.H_subset_Hbar).tendsto
    rwa [hzero ξ hξ] at h
  have : NeBot (𝓝[H] (ξ : ℂ)) := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp only [Complex.ofReal_im]))
  have he := tendsto_nhds_unique (((hU.comp hφ).sub hC).sub (hLlim.const_mul χ))
    hStoppedGermComparison
  linarith only [he]

end InteractingSLE.Sec7.PocketStopSide
