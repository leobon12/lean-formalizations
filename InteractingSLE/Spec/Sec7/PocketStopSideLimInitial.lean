/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideLimTime
import InteractingSLE.Spec.Sec7.Lemma71BStop

/-!
# The zero-time side limit and the all-time canonical reduction

PROVE-STRIPSYS38. At time zero the two geometric seed coordinates coincide,
so the exposed interval is empty and the phase term is identically zero.
Causality proves this even when the canonical driver is only locally continuous.
Together with the positive-lifetime argument this supplies all q, as required
by the per-q pocket-word inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketTraversal PocketAdapt Lemma71C PocketStop PhaseSel

/-- The geometric image of the seed at time zero only uses the driver's value
at zero; global continuity of that driver is unnecessary. -/
theorem rightImg_seed_zero_time {w : ℝ → ℝ} (hw₀ : w 0 = 0) :
    MartChar.RealFlow.rightImg w 0 0 = 0 := by
  have heq : EqOn w (fun _ => 0) (Icc 0 0) := by
    intro r hr
    have hr₀ : r = 0 := le_antisymm hr.2 hr.1
    rwa [hr₀]
  rw [Lemma71B.rightImg_congr continuous_const le_rfl heq]
  exact MartChar.RealFlow.rightImg_zero continuous_const rfl le_rfl

/-- With both seed marks at zero, a phase side limit at relative time zero is
already canonical, since it has no exposed interval. -/
theorem pocketStopSideLimit_zero_of_phase {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {c : Ω → Chart} {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {K : Ω → Set ℂ} {δ : Ω → ℝ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hseedR : ∀ ω ∈ A, xR ω 0 = 0)
    (hPhase : PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u K δ 0) :
    PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u K 0 := by
  intro g hg
  filter_upwards [hPhase.2 g hg] with ω hs hω hq v hv hvr ξ hξ
  have hR : geomRW (fun t ω => segDriver (γ ω) t) xR 0 0 ω = 0 := by
    change MartChar.RealFlow.rightImg (Bessel.realPath (fun t ω => segDriver (γ ω) t) ω) (xR ω 0) 0 = 0
    rw [hseedR ω hω]
    apply rightImg_seed_zero_time
    simpa only [Bessel.realPath, Real.toNNReal_zero] using (hγ ω hω).segDriver_spec.1
  have hL : geomLW (fun t ω => segDriver (γ ω) t) xL 0 0 ω = 0 := by
    change -MartChar.RealFlow.rightImg
      (Bessel.realPath (fun t ω => -segDriver (γ ω) t) ω) (-xL ω 0) 0 = 0
    rw [hseedL ω hω, neg_zero, rightImg_seed_zero_time (by
      simp only [Bessel.realPath, Real.toNNReal_zero, (hγ ω hω).segDriver_spec.1, neg_zero]), neg_zero]
  have h := hs hω hq v hv hvr ξ hξ
  simpa only [phaseData, hL, hR, Ioo_self, indicator_empty, Pi.zero_apply, mul_zero, add_zero] using h

/-- All-time side limits for the per-q consumers. Only the common phase
continuity and one positive anchor remain, besides the phase boundary word. -/
theorem pocketStopSideLimit_of_phase_common_anchor {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {κ : ℝ} (hκ : 4 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {c : Ω → Chart} {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {K : ℝ≥0 → Ω → Set ℂ} {δ : ℝ≥0 → Ω → ℝ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hseedR : ∀ ω ∈ A, xR ω 0 = 0)
    (hPhase : ∀ q, PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u (K q) (δ q) q)
    (hPhaseContinuous : ∀ᵐ ω ∂P, ω ∈ A →
      ContinuousOn (fun t => δ t ω) {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)})
    (hAnchor : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < capLife (γ ω) ∧ δ s ω = 0) :
    ∀ q, PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u (K q) q := by
  intro q
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ q from bot_le) with hq | hq
  · subst q
    exact pocketStopSideLimit_zero_of_phase hγ hseedL hseedR (hPhase 0)
  · exact pocketStopSideLimit_of_phase_continuous_anchor hκ hPhase hPhaseContinuous hAnchor q hq

end InteractingSLE.Sec7.PocketStopSide
