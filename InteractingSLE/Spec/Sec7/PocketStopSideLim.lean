/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideLimAnchor
import InteractingSLE.Spec.Sec7.PocketStopSideLimInitial
import InteractingSLE.Spec.Sec7.PocketStopSideLimPieces
import InteractingSLE.Spec.Sec7.PocketWordPerQSide

/-!
# Canonical side limits from phase words and countably selected R.6 anchors

PROVE-STRIPSYS38. `ae_phase_eq_zero_of_inner_zero` supplies a zero phase at a
fixed relative time from the inner canonical side limit and the shared-side
comparison. A rational original visit can have a random relative time: the
corresponding `hZero` must therefore be proved jointly for each candidate event.
Intersect those statements over the countable candidates before selecting a
realized visit. The continuous common phase is then zero at every positive time;
the zero-time exposed interval is empty. The output has the all-q shape required
by `PocketWordPerQ.PocketSideLimitInput0` and its Inf version.

The actual phase-cover and nested-germ producers remain explicit in LimPieces
and LimAnchor. These reductions do not prove the unconditional strip theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketTraversal Lemma71C PocketStop

/-- Countably many candidate R.6 visits can be selected after taking a common
probability-one event. No selected time is substituted into a merely per-time
almost-sure statement. -/
theorem ae_phase_anchor_of_countable_visits {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {A : Set Ω} {γ : Ω → ℝ → ℂ} {δ : ℝ≥0 → Ω → ℝ}
    {s : ι → Ω → ℝ≥0} {E : ι → Set Ω}
    (hZero : ∀ i, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ E i → δ (s i ω) ω = 0)
    (hVisits : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ i, 0 < s i ω ∧ (s i ω : ℝ≥0∞) < capLife (γ ω) ∧ ω ∈ E i) :
    ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ t : ℝ≥0, 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω) ∧ δ t ω = 0 := by
  filter_upwards [ae_all_iff.2 hZero, hVisits] with ω hzero hvisit hω hT
  obtain ⟨i, hi, hiT, hEi⟩ := hvisit hω hT
  exact ⟨s i ω, hi, hiT, hzero i hω hEi⟩

/-- The all-time canonical side limit, ready for either per-q pocket-word
consumer, from a common phase word, its continuity, and countable R.6 anchors.
The candidate comparison `hZero` is a joint statement at the possibly random
relative time. A merely per-time conclusion of `ae_phase_eq_zero_of_inner_zero`
cannot be evaluated at this time without a further joint comparison. -/
theorem pocketStopSideLimit_of_phase_countable_anchors {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
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
    {s : ι → Ω → ℝ≥0} {E : ι → Set Ω}
    (hZero : ∀ i, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ E i → δ (s i ω) ω = 0)
    (hVisits : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ i, 0 < s i ω ∧ (s i ω : ℝ≥0∞) < capLife (γ ω) ∧ ω ∈ E i) :
    ∀ q, PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u (K q) q :=
  pocketStopSideLimit_of_phase_common_anchor hκ hγ hseedL hseedR hPhase hPhaseContinuous
    (ae_phase_anchor_of_countable_visits hZero hVisits)

end InteractingSLE.Sec7.PocketStopSide
