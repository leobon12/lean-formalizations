/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrFlow
import InteractingSLE.Spec.Sec7.R6TrLanding

/-!
# The exact remaining common-time geometric input

PROVE-R6-TWO. `SameTimeLeftData` records the same-original-time
incident interval of Astra §2 and the two physical balls of §4.
It is a named, unproved geometric input, not a source theorem.
No later time, non-corner condition, or singleton exposed landing occurs.
The subsequent window theorem proves all later-time conclusions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.R6Tr

open PocketStopSide R6Safe

/-- The ordinary one-pocket data provided by `R6Fc.chart_facts` or
`chart_factsInf`, restricted to a real capacity interval. -/
structure InnerChain (V P : Set ℂ) (I : ℝ → Chart) (p : ℂ) where
  coord : ℂ → ℂ
  inverse : ℂ → ℂ
  driver : ℝ → ℝ
  time : ℝ
  horizon : ℝ
  time_pos : 0 < time
  horizon_pos : 0 < horizon
  coord_bij : SupercriticalConformalCovariance.IsConformalBijection coord V H
  mem_boundary : V ⊆ P
  coord_cont : ContinuousOn coord P
  inverse_eq : EqOn inverse (Function.invFunOn coord V) H
  driver_cont : Continuous driver
  driver_zero : driver 0 = 0
  tip_cont : ContinuousOn (fun z => inverse (extendFrom H (fwdMapInv driver time) z)) Hbar
  tip_eq : inverse (extendFrom H (fwdMapInv driver time) 0) = p
  dom_eq : ∀ q ∈ Ico time (time + horizon), ((I q).dom : Set ℂ) = V ∩ coord ⁻¹' (H \ fwdHull driver q)
  conformal : ∀ q ∈ Ico time (time + horizon), (I q).IsConformal
  forward_eq : ∀ q ∈ Ico time (time + horizon), ∀ w ∈ V, (I q).1 w = fwdMap driver q (coord w)
  inverse_cont : ∀ q ∈ Ico time (time + horizon),
    ∃ E : ℂ → ℂ, EqOn E (I q).2.1 H ∧ ContinuousOn E Hbar

/-- **Named remaining common-time geometry.** Supply this for each of
the three two-outer shapes on the geometric event, at the original
visit time and before growing the inner hull. This is the common input
for finite and infinite targets. Its force landing may be a seed corner.

The compact interval is inside the shared incident interval of the two
ambient Jordan faces. The exposed and shared test points, their real
transition limits, and their physical balls are selected only once. -/
structure SameTimeLeftData (O I₀ : Chart) (EO : ℂ → ℂ) (P : Set ℂ) (p : ℂ) (v w : ℝ) where
  compact : Set ℝ
  interval : Set ℝ
  shared : ℝ
  exposed : ℝ
  boundary : ℝ → ℝ
  isCompact : IsCompact compact
  interval_subset : interval ⊆ compact
  isOpen : IsOpen interval
  isPreconnected : IsPreconnected interval
  shared_mem : shared ∈ interval
  exposed_mem : exposed ∈ interval
  shared_lt : shared < v
  lt_exposed : v < exposed
  exposed_neg : exposed < 0
  inclusion : (I₀.dom : Set ℂ) ⊆ O.dom
  collars : ∀ x ∈ compact, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ O.1 '' (I₀.dom : Set ℂ)
  avoids_tip : ∀ x ∈ compact, EO (x : ℂ) ≠ p
  landing_mem : ∀ x ∈ interval, EO (x : ℂ) ∈ P
  boundary_limit : ∀ x ∈ interval, Tendsto (pocketTransitionChart O I₀).1
    (𝓝[((pocketTransitionChart O I₀).dom : Set ℂ)] (x : ℂ)) (𝓝 (boundary x : ℂ))
  shared_image_lt : boundary shared < w
  lt_exposed_image : w < boundary exposed
  exposed_image_neg : boundary exposed < 0
  shared_ball : ∃ e > 0, (O.dom : Set ℂ) ∩ ball (EO (shared : ℂ)) e ⊆ I₀.dom
  exposed_ball : ∃ e > 0, (O.dom : Set ℂ) ∩ ball (EO (exposed : ℂ)) e ⊆ I₀.dom

/-- `R6FaceR` with its interval and outer test coordinates displayed,
so that uniformity across later real times is part of the type. -/
def FaceAt (ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ) (O I : Chart)
    (J : Set ℝ) (y ξ : ℝ) : Prop :=
  ∃ η₀ η : ℝ, IsOpen J ∧ IsPreconnected J ∧
    (∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ ((pocketTransitionChart O I).dom : Set ℂ)) ∧
    (∀ x ∈ J, ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart O I).1 z‖ ≤ M) ∧
    y ∈ J ∧ ξ ∈ J ∧
    Tendsto (pocketTransitionChart O I).1 (𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (y : ℂ)) (𝓝 (η₀ : ℂ)) ∧
    Tendsto (pocketTransitionChart O I).1 (𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (ξ : ℂ)) (𝓝 (η : ℂ)) ∧
    ((vR 0 < y ∧ wR 0 < η₀ ∧ ρR 0 = σR 0) ∨ (y < vL 0 ∧ η₀ < wL 0 ∧ ρL 0 = σL 0)) ∧
    ((0 < ξ ∧ ξ < vR 0 ∧ 0 < η ∧ η < wR 0) ∨ (vL 0 < ξ ∧ ξ < 0 ∧ wL 0 < η ∧ η < 0)) ∧
    (∀ p : ℂ, Tendsto O.2.1 (𝓝[H] (y : ℂ)) (𝓝 p) →
      ∃ e > 0, (H \ (I.dom : Set ℂ)) ∩ ball p e ⊆ H \ (O.dom : Set ℂ)) ∧
    (∀ p : ℂ, Tendsto O.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
      ∃ e > 0, (H \ (I.dom : Set ℂ)) ∩ ball p e ⊆ H \ (O.dom : Set ℂ))

theorem FaceAt.r6FaceR {ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ} {O I : Chart}
    {J : Set ℝ} {y ξ : ℝ} (h : FaceAt ρL ρR σL σR vL vR wL wR O I J y ξ) :
    R6FaceR ρL ρR σL σR vL vR wL wR O I (H \ (O.dom : Set ℂ)) (H \ (I.dom : Set ℂ)) := by
  obtain ⟨η₀, η, h⟩ := h
  exact ⟨J, y, η₀, ξ, η, h⟩

end InteractingSLE.Sec7.R6Tr
