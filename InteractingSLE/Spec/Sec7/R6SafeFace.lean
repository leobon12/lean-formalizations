/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FinGeomCore
import InteractingSLE.Spec.Sec7.PocketSideInReachExtension
import InteractingSLE.Spec.Sec7.PocketSideInLogTransition
import InteractingSLE.Spec.Sec7.PocketStopSideInputsGeometry
import InteractingSLE.Spec.Sec7.Aux29CorSide

/-!
# R.6's current-face geometry: `R6GeomCore` from a face description (deterministic)

PROVE-R6-SAFE. PROVE-R6-CERT2 reduced R.6's pathwise inputs to `R6Fin.R6GeomCore` (the transition reflecting across
a connected real interval `J` with its inherited logarithm, collars at a shared-side point `y₀` and an exposed point
`ξ`, heights, landings and local agreement). This file discharges all of its complex-analytic content from the
landed `PocketStopSide` tools, leaving only the face description of the source's Lemma R.6 (supplement p. 476: "the
active `U` domain is a Jordan subdomain sharing a connected open real interval `J` with `ℍ`, incident from above"):

* **`r6GeomCore_of_face`**: `R6GeomCore` from the inclusion of the two current domains, an open connected `J` with
  collars (half-discs of the outer chart in the transition domain) and local bounds of the transition, the outer
  landings along `J`, a continuous boundary extension of the inner inverse, derivative logarithms of the two charts
  carrying their lifts, the limits of the transition at `y₀` and `ξ` with the side/jump/height conditions at these
  points, and the local agreement of the two active complements near the two landings. The reflection
  (`PocketStopSide.exists_transition_extension_of_inverse_and_bounds`), the inherited logarithm
  (`PocketStopSide.exists_current_pocket_log_extension`) and the two `R6Rel.R6Collar`s are constructed.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R6Safe

open R6Fin R6Rel PocketStopSide

/-- Along the outer half-plane at a point with a collar, the transition chart's forward map and any extension of it
converge to the transition's limit, inside `ℍ`. -/
theorem tendsto_extension_of_collar {outer inner : Chart} (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hIncl : (inner.dom : Set ℂ) ⊆ outer.dom) {G : ℂ → ℂ}
    (hGeq : EqOn G (pocketTransitionChart outer inner).1 (pocketTransitionChart outer inner).dom) {y η : ℝ}
    (hcol : ∃ r > 0, H ∩ ball (y : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ))
    (hlim : Tendsto (pocketTransitionChart outer inner).1
      (𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (y : ℂ)) (𝓝 (η : ℂ))) :
    Tendsto G (𝓝[H] (y : ℂ)) (𝓝[H] (η : ℂ)) := by
  have hT := isConformal_pocketTransitionChart hO hI hIncl
  obtain ⟨r, hr, hsub⟩ := hcol
  have hmem : ((pocketTransitionChart outer inner).dom : Set ℂ) ∈ 𝓝[H] (y : ℂ) :=
    mem_nhdsWithin.2 ⟨ball (y : ℂ) r, isOpen_ball, mem_ball_self hr, fun z hz => hsub ⟨hz.2, hz.1⟩⟩
  have hle : 𝓝[H] (y : ℂ) ≤ 𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (y : ℂ) :=
    nhdsWithin_le_iff.2 hmem
  have heq : (pocketTransitionChart outer inner).1 =ᶠ[𝓝[H] (y : ℂ)] G :=
    Filter.mem_of_superset hmem fun z hz => (hGeq hz).symm
  refine tendsto_nhdsWithin_iff.2 ⟨(hlim.mono_left hle).congr' heq, ?_⟩
  filter_upwards [hmem] with z hz
  rw [hGeq hz]
  exact hT.fwd_mem hz

/-- **`R6GeomCore` from a face description** (deterministic; the source's Lemma R.6 hypotheses, supplement p. 476):
the reflection across `J`, the inherited logarithm and the two collars are constructed from the landed
`PocketStopSide` tools. -/
theorem r6GeomCore_of_face {κ : ℝ} {nL nR mL mR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {σL : Fin (mL + 1) → ℝ} {σR : Fin (mR + 1) → ℝ} {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ}
    {wL : Fin (mL + 1) → ℝ} {wR : Fin (mR + 1) → ℝ} {outer inner : Chart} {EC EU : Set ℂ}
    (hO : outer.IsConformal) (hI : inner.IsConformal) (hIncl : (inner.dom : Set ℂ) ⊆ outer.dom)
    {E : ℂ → ℂ} (hE : EqOn E inner.2.1 H) (hEc : ContinuousOn E Hbar)
    {LO LI : ℂ → ℂ} (hLO : IsDerivLog outer.1 LO outer.dom) (hLI : IsDerivLog inner.1 LI inner.dom)
    (hOl : ∀ p ∈ (outer.dom : Set ℂ), outer.2.2 p = (LO p).im)
    (hIl : ∀ p ∈ (inner.dom : Set ℂ), inner.2.2 p = (LI p).im)
    {J : Set ℝ} (hJo : IsOpen J) (hJ : IsPreconnected J)
    (hCollars : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ))
    {p : ℝ → ℂ} (hLanding : ∀ x ∈ J, Tendsto outer.2.1 (𝓝[H] (x : ℂ)) (𝓝 (p x)))
    (hBound : ∀ x ∈ J, ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart outer inner).1 z‖ ≤ M)
    {y₀ η₀ ξ η : ℝ} (hy₀ : y₀ ∈ J) (hξ : ξ ∈ J)
    (hlim₀ : Tendsto (pocketTransitionChart outer inner).1
      (𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (y₀ : ℂ)) (𝓝 (η₀ : ℂ)))
    (hlim : Tendsto (pocketTransitionChart outer inner).1
      (𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (ξ : ℂ)) (𝓝 (η : ℂ)))
    (h₀ : y₀ ∉ forceJumpSet vL vR ∧ y₀ ∉ Ioo (vL 0) (vR 0) ∧ η₀ ∉ forceJumpSet wL wR ∧
      η₀ ∉ Ioo (wL 0) (wR 0) ∧ forceBoundaryData κ ρL ρR vL vR y₀ = forceBoundaryData κ σL σR wL wR η₀)
    (h₁ : ξ ∉ forceJumpSet vL vR ∧ ξ ∈ Ioo (vL 0) (vR 0) ∧ η ∉ forceJumpSet wL wR ∧ η ∈ Ioo (wL 0) (wR 0) ∧
      forceBoundaryData κ ρL ρR vL vR ξ = forceBoundaryData κ σL σR wL wR η)
    (hag₀ : ∃ ε > 0, EU ∩ ball (p y₀) ε ⊆ EC) (hag : ∃ ε > 0, EU ∩ ball (p ξ) ε ⊆ EC) :
    R6GeomCore κ ρL ρR σL σR vL vR wL wR outer inner EC EU := by
  obtain ⟨G, hGeq, -, hGr, -⟩ :=
    exists_transition_extension_of_inverse_and_bounds hO hI hIncl hE hEc hJo hCollars hLanding hBound
  obtain ⟨Lg, -, hLgim, hLgc, hLgbar, hLgexp⟩ :=
    exists_current_pocket_log_extension hO hI hIncl hLO hLI hOl hIl hGeq hJo hCollars hGr
  have htr : R6Transition outer inner J G Lg := ⟨hO, hI, hIncl, hJ, hGr, hLgc, hLgexp, hGeq, hLgim⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := h₀
  obtain ⟨b1, b2, b3, b4, b5⟩ := h₁
  exact ⟨J, G, Lg, y₀, η₀, ξ, η, p y₀, p ξ, htr,
    ⟨⟨hy₀, hCollars y₀ hy₀, hLgbar y₀ hy₀,
      tendsto_extension_of_collar hO hI hIncl hGeq (hCollars y₀ hy₀) hlim₀⟩, a1, a2, a3, a4, a5,
      hLanding y₀ hy₀, hag₀⟩,
    ⟨⟨hξ, hCollars ξ hξ, hLgbar ξ hξ, tendsto_extension_of_collar hO hI hIncl hGeq (hCollars ξ hξ) hlim⟩,
      b1, b2, b3, b4, b5, hLanding ξ hξ, hag⟩⟩

/-- **The face description of R.6** (the hypotheses of the source's Lemma R.6 together with the application's point
choices, supplement p. 476): the inner current domain lies in the outer one; an open connected real interval `J` of
the outer chart has collars in the transition domain and local bounds of the transition; at a shared-side point `y₀`
and an exposed point `ξ` of `J` the transition has real limits `η₀`, `η` with the side, jump and height conditions;
the two active complements agree locally (one inclusion) near the outer landings at `y₀` and `ξ`. It mentions no
logarithm, reflection or extension. -/
def R6Face (κ : ℝ) {nL nR mL mR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (σL : Fin (mL + 1) → ℝ)
    (σR : Fin (mR + 1) → ℝ) (vL : Fin (nL + 1) → ℝ) (vR : Fin (nR + 1) → ℝ) (wL : Fin (mL + 1) → ℝ)
    (wR : Fin (mR + 1) → ℝ) (outer inner : Chart) (EC EU : Set ℂ) : Prop :=
  (inner.dom : Set ℂ) ⊆ outer.dom ∧ ∃ (J : Set ℝ) (y₀ η₀ ξ η : ℝ), IsOpen J ∧ IsPreconnected J ∧
    (∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ)) ∧
    (∀ x ∈ J, ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart outer inner).1 z‖ ≤ M) ∧
    y₀ ∈ J ∧ ξ ∈ J ∧
    Tendsto (pocketTransitionChart outer inner).1
      (𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (y₀ : ℂ)) (𝓝 (η₀ : ℂ)) ∧
    Tendsto (pocketTransitionChart outer inner).1
      (𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (ξ : ℂ)) (𝓝 (η : ℂ)) ∧
    (y₀ ∉ forceJumpSet vL vR ∧ y₀ ∉ Ioo (vL 0) (vR 0) ∧ η₀ ∉ forceJumpSet wL wR ∧
      η₀ ∉ Ioo (wL 0) (wR 0) ∧ forceBoundaryData κ ρL ρR vL vR y₀ = forceBoundaryData κ σL σR wL wR η₀) ∧
    (ξ ∉ forceJumpSet vL vR ∧ ξ ∈ Ioo (vL 0) (vR 0) ∧ η ∉ forceJumpSet wL wR ∧ η ∈ Ioo (wL 0) (wR 0) ∧
      forceBoundaryData κ ρL ρR vL vR ξ = forceBoundaryData κ σL σR wL wR η) ∧
    (∀ p : ℂ, Tendsto outer.2.1 (𝓝[H] (y₀ : ℂ)) (𝓝 p) → ∃ ε > 0, EU ∩ ball p ε ⊆ EC) ∧
    (∀ p : ℂ, Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → ∃ ε > 0, EU ∩ ball p ε ⊆ EC)

/-- **`R6GeomCore` from the face description and the generic chart facts** (conformal charts, a continuous boundary
extension of the inner inverse, outer landings at every real point, derivative logarithms carrying the lifts). -/
theorem r6GeomCore_of_r6Face {κ : ℝ} {nL nR mL mR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {σL : Fin (mL + 1) → ℝ} {σR : Fin (mR + 1) → ℝ} {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ}
    {wL : Fin (mL + 1) → ℝ} {wR : Fin (mR + 1) → ℝ} {outer inner : Chart} {EC EU : Set ℂ}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    {E : ℂ → ℂ} (hE : EqOn E inner.2.1 H) (hEc : ContinuousOn E Hbar)
    (hland : ∀ x : ℝ, ∃ p : ℂ, Tendsto outer.2.1 (𝓝[H] (x : ℂ)) (𝓝 p))
    {LO LI : ℂ → ℂ} (hLO : IsDerivLog outer.1 LO outer.dom) (hLI : IsDerivLog inner.1 LI inner.dom)
    (hOl : ∀ p ∈ (outer.dom : Set ℂ), outer.2.2 p = (LO p).im)
    (hIl : ∀ p ∈ (inner.dom : Set ℂ), inner.2.2 p = (LI p).im)
    (hface : R6Face κ ρL ρR σL σR vL vR wL wR outer inner EC EU) :
    R6GeomCore κ ρL ρR σL σR vL vR wL wR outer inner EC EU := by
  obtain ⟨hIncl, J, y₀, η₀, ξ, η, hJo, hJ, hCollars, hBound, hy₀, hξ, hlim₀, hlim, h₀, h₁, hag₀, hag⟩ := hface
  choose p hp using hland
  exact r6GeomCore_of_face hO hI hIncl hE hEc hLO hLI hOl hIl hJo hJ hCollars (p := p) (fun x _ => hp x) hBound hy₀
    hξ hlim₀ hlim h₀ h₁ (hag₀ _ (hp y₀)) (hag _ (hp ξ))

/-! ### The generic facts of a live current pocket chart -/

section Generic

open PocketStop PocketStopField PocketTraversal Lemma71C

variable {Ω : Type*} {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {γ : Ω → ℝ → ℂ} {q : ℝ≥0}

/-- **The generic facts of a live current chart of a pocket traversal** (the branch-shifted Jordan chart of a Jordan
pocket, followed by the relative Loewner map): it is conformal, its inverse extends continuously to `ℍ̄`, it has a
landing at every real point, and it has a derivative logarithm carrying its lift. -/
theorem relChart_generic (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) {ω : Ω} (hω : ω ∈ A) (hγ : IsDrivenCurve (γ ω))
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) {seed : ℂ}
    (hJordan : (∃ pole : ℂ, Bornology.IsBounded (C ω) ∧ pole ∉ C ω ∧ Sec6.IsJordanCoord (C ω) pole seed (ψ ω)) ∨
      Sec6.IsJordanCoordInf (C ω) seed (ψ ω)) :
    (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).IsConformal ∧
      (∃ E : ℂ → ℂ, EqOn E (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).2.1 H ∧
        ContinuousOn E Hbar) ∧
      (∀ x : ℝ, ∃ p : ℂ,
        Tendsto (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) ∧
      ∃ L : ℂ → ℂ, IsDerivLog (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).1 L
          (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).dom ∧
        ∀ z ∈ (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).dom,
          (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).2.2 z = (L z).im := by
  obtain ⟨-, -, hpc, hpd⟩ := pChart_props hCo hCH hψ ω
  have hb : (shiftChart (pChart A C ψ ω) (n ω)).IsConformal := hpc
  have hbdom : ((shiftChart (pChart A C ψ ω) (n ω)).dom : Set ℂ) = C ω := by
    change ((pChart A C ψ ω).dom : Set ℂ) = C ω
    rw [hpd]
    ext z
    simp only [mem_ofPred_eq, hω, true_and, not_true_eq_false, false_and, or_false]
  have hbeq : EqOn (shiftChart (pChart A C ψ ω) (n ω)).1 (ψ ω) (C ω) := fun z _ => by
    change pFwd A ψ ω z = ψ ω z
    rw [pFwd_of_mem hω]
  obtain ⟨E₀, hE₀, hE₀c, -⟩ := PocketStopSide.exists_inverse_extension_of_jordan_cases hJordan hb hbdom hbeq
  obtain ⟨F, hF, hFc, -⟩ := PocketStopSide.exists_relative_inverse_extension
    (c := fun ω => shiftChart (pChart A C ψ ω) (n ω)) hγ hq hE₀ hE₀c
  refine ⟨isConformal_relChart_of_driven hγ hq hb, ⟨F, hF, hFc⟩, fun x => ⟨F x, ?_⟩, ?_⟩
  · have hx : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
    exact (((hFc _ hx).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
      (eventually_nhdsWithin_of_forall fun _ hw => hF hw)
  · have hlog := isDerivLog_pLog hCo hψ hω
    have hℓ : IsDerivLog (shiftChart (pChart A C ψ ω) (n ω)).1
        (fun z => pLog A C ψ ω z - (n ω : ℂ) * (2 * π * Complex.I))
        (shiftChart (pChart A C ψ ω) (n ω)).dom := by
      rw [hbdom]
      refine ⟨hlog.1.sub_const _, fun z hz => ?_⟩
      rw [Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]
      exact hlog.2 z hz
    refine Aux29Cor.exists_isDerivLog_relChart (c := fun ω => shiftChart (pChart A C ψ ω) (n ω)) hγ hq hb hℓ
      fun z _ => ?_
    change (pLog A C ψ ω z).im - 2 * π * (n ω) = (pLog A C ψ ω z - (n ω : ℂ) * (2 * π * Complex.I)).im
    simp only [Complex.sub_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    ring

end Generic

end InteractingSLE.Sec7.R6Safe
