/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRefPhase

/-!
# R.6 anchors at countably many random relative visit times

PROVE-POCKET-SIDEIN, R73 §3.3. The germ comparison is joint in the sample at
each candidate's actual relative time. R.6 is applied on that event; only then
is the countable family intersected and a realized visit selected. The exact
shared-side geometry and germ identification remain the named `hJointGerms`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketTraversal Lemma71C PocketStop PhaseSel

/-- The deterministic shared-side anchor applies jointly at a candidate's
random relative time. No per-fixed-time almost-sure assertion is evaluated there. -/
theorem ae_phase_zero_of_joint_germs {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {κ : ℝ} (hκ : 4 < κ) {A : Set Ω} {E : ι → Set Ω}
    {δ : ℝ≥0 → Ω → ℝ} {s : ι → Ω → ℝ≥0}
    {MC MU : ι → Ω → ℂ → ℝ}
    (hJointGerms : ∀ i, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ E i →
      ∃ (ξ η y₀ : ℝ) (J : Set ℝ) (φ L : ℂ → ℂ) (bC bU b : ℝ),
        IsPreconnected J ∧ ξ ∈ J ∧ y₀ ∈ J ∧
        (∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal φ y r) ∧
        ContinuousOn (fun y : ℝ => L y) J ∧
        (∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect φ) y) ∧
        bC = bU ∧ bU = bC + chiC κ * (L y₀).im ∧
        ContinuousWithinAt L Hbar (ξ : ℂ) ∧
        Tendsto φ (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ)) ∧
        Tendsto (MC i ω) (𝓝[H] (ξ : ℂ)) (𝓝 (b + δ (s i ω) ω)) ∧
        Tendsto (MU i ω) (𝓝[H] (η : ℂ)) (𝓝 b) ∧
        Tendsto (fun z => MU i ω (φ z) - MC i ω z - chiC κ * (L z).im)
          (𝓝[H] (ξ : ℂ)) (𝓝 0)) :
    ∀ i, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ E i → δ (s i ω) ω = 0 := by
  have hχ : chiC κ ≠ 0 := by
    intro he
    apply phaseStep_ne_zero hκ
    rw [phaseStep, he, neg_zero, mul_zero]
  intro i
  filter_upwards [hJointGerms i] with ω hω hA hE
  obtain ⟨ξ, η, y₀, J, φ, L, bC, bU, b, hJ, hξ, hy₀, hloc, hLc, hexp,
    hsame, htransform, hLξ, hφ, hC, hU, hcompare⟩ := hω hA hE
  exact phase_eq_zero_of_inner_germ hχ hJ hloc hLc hexp hy₀ hsame htransform
    hξ hLξ hφ hC hU hcompare

/-- A nonempty open set of original visit times supplies a rational candidate.
Clock bounds and candidate membership are intersected over Q before selection. -/
theorem ae_visits_of_open_original_times {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A : Set Ω} {γ : Ω → ℝ → ℂ} {V : Ω → Set ℝ}
    {s : ℚ → Ω → ℝ≥0} {E : ℚ → Set Ω}
    (hOpen : ∀ᵐ ω ∂P, ω ∈ A → IsOpen (V ω))
    (hNonempty : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) → (V ω).Nonempty)
    (hClock : ∀ r : ℚ, ∀ᵐ ω ∂P, ω ∈ A → (r : ℝ) ∈ V ω →
      0 < s r ω ∧ (s r ω : ℝ≥0∞) < capLife (γ ω) ∧ ω ∈ E r) :
    ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ r : ℚ, 0 < s r ω ∧ (s r ω : ℝ≥0∞) < capLife (γ ω) ∧ ω ∈ E r := by
  filter_upwards [hOpen, hNonempty, ae_all_iff.2 hClock] with ω ho hn hc hω hT
  obtain ⟨r, hr⟩ := Rat.denseRange_cast.exists_mem_open (ho hω) (hn hω hT)
  exact ⟨r, hc r hω hr⟩

/-- R73's whole-lifetime conclusion, with phase continuity obtained from the
mean probes and the zero visits obtained from joint shared-side germs. -/
theorem pocketStopSideLimit_of_phase_probes_joint_germs {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι] {P : Measure Ω} {κ : ℝ} (hκ : 4 < κ)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {K : ℝ≥0 → Ω → Set ℂ} {δ : ℝ≥0 → Ω → ℝ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hseedR : ∀ ω ∈ A, xR ω 0 = 0)
    (hPhase : ∀ q, PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u (K q) (δ q) q)
    {M M₀ w : ℕ → Ω → ℝ≥0 → ℝ}
    (hProbes : ∀ N : ℕ, ∀ᵐ ω ∂P, ω ∈ A →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (M N ω) S ∧ ContinuousOn (M₀ N ω) S ∧ ContinuousOn (w N ω) S ∧
        ∀ t ∈ S, 0 < w N ω t ∧ M N ω t - M₀ N ω t = δ t ω * w N ω t)
    {s : ι → Ω → ℝ≥0} {E : ι → Set Ω}
    {MC MU : ι → Ω → ℂ → ℝ}
    (hJointGerms : ∀ i, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ E i →
      ∃ (ξ η y₀ : ℝ) (J : Set ℝ) (φ L : ℂ → ℂ) (bC bU b : ℝ),
        IsPreconnected J ∧ ξ ∈ J ∧ y₀ ∈ J ∧
        (∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal φ y r) ∧
        ContinuousOn (fun y : ℝ => L y) J ∧
        (∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect φ) y) ∧
        bC = bU ∧ bU = bC + chiC κ * (L y₀).im ∧
        ContinuousWithinAt L Hbar (ξ : ℂ) ∧
        Tendsto φ (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ)) ∧
        Tendsto (MC i ω) (𝓝[H] (ξ : ℂ)) (𝓝 (b + δ (s i ω) ω)) ∧
        Tendsto (MU i ω) (𝓝[H] (η : ℂ)) (𝓝 b) ∧
        Tendsto (fun z => MU i ω (φ z) - MC i ω z - chiC κ * (L z).im)
          (𝓝[H] (ξ : ℂ)) (𝓝 0))
    (hVisits : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ i, 0 < s i ω ∧ (s i ω : ℝ≥0∞) < capLife (γ ω) ∧ ω ∈ E i) :
    ∀ q, PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u (K q) q :=
  pocketStopSideLimit_of_phase_mean_probes hκ hγ hseedL hseedR hPhase hProbes
    (ae_phase_zero_of_joint_germs hκ hJointGerms) hVisits

end InteractingSLE.Sec7.PocketStopSide
