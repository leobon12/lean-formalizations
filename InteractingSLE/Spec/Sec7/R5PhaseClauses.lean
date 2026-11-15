/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5PhaseTest

/-!
# Lemma R.5's remaining clauses at one relative capacity, for any pocket test

Packet PROVE-R5-PHASE. `R5Clauses` bundles exactly the parts of Lemma R.5 (spec pp. 474–475) that are not
deterministic chart facts or the raw reference laws, for one pocket test, one word and one relative capacity `q`,
against a countable family of old references `F i` normalized at relative level `0`:

1. a finite exceptional physical set `X` (the attachments, the current tip, the pocket target, marked points);
2. the phase `δ` is lattice-valued on the live event;
3. reference charts `old i` on pair events `M i` (the reference domain contains the current one);
4. **the old-chart increment laws** (the nested marked local-set law at the enlarged stop, for every version of the
   reference and current means);
5. **the cover**: every real current coordinate off the force jumps whose physical landing avoids `X` has an unfilled
   incident half-disc in some reference chart, the reference's exact height `b`, the limiting lift difference `d`, and
   `b + χ d` equal to the phase-shifted word.

`pocketStopPhaseSideLimit_of_r5Clauses`: with the raw reference laws and the base chart's data, these clauses give
the phase side limit (`R5Phase.pocketStopPhaseSideLimit_of_incrementLaws_offExc`). No margin, weight or word
restriction. Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Phase

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling
  Aux119Heights PocketStopSide PhaseSel Aux29Cor

/-- **Lemma R.5's remaining clauses at the relative capacity `q`** (see the module docstring), for references
`liveExt A γ C (F i) 0`. -/
def R5Clauses {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (A : Set Ω) (γ : Ω → ℝ → ℂ)
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart) (a : ℝ)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) (C : Ω → Set ℂ) (F : ℕ → Ω → Set ℂ) (δ : Ω → ℝ)
    (X : Ω → Set ℂ) (liftB : ℕ → Ω → ℂ → ℝ) (M : ℕ → Set Ω) (old : ℕ → Ω → Chart) (q : ℝ≥0) : Prop :=
  (∀ ω, (X ω).Finite) ∧
  (∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ m : ℤ, δ ω = m * phaseStep κ) ∧
  (∀ i, ∀ ω ∈ M i, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧ (old i ω).IsConformal ∧
    ((relChart c γ q ω).dom : Set ℂ) ⊆ (old i ω).dom ∧
    ((old i ω).dom : Set ℂ) = H \ liveExt A γ C (F i) 0 ω) ∧
  (∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ i, IsLocalSetMean (liveExt A γ C (F i) 0) h₀ P (gB i)) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
    ∀ i, HasOldChartIncrementLaw P (M i) (old i) (relChart c γ q) (gB i) g) ∧
  ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ i, IsLocalSetMean (liveExt A γ C (F i) 0) h₀ P (gB i)) →
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
      extendFrom H (relChart c γ q ω).2.1 ξ ∉ X ω →
      ∃ (i : ℕ) (x r b d : ℝ), ω ∈ M i ∧ 0 < r ∧
        (old i ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (relChart c γ q ω).dom ∧
        Tendsto (fun z => (old i ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
        Tendsto (fun y => harmRep (gB i ω) (H \ liveExt A γ C (F i) 0 ω) ((relChart c γ q ω).2.1 y) +
            u ((relChart c γ q ω).2.1 y) + chiC κ * liftB i ω ((relChart c γ q ω).2.1 y))
          (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
        Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
            liftB i ω ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
        b + chiC κ * d = phaseData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)
          (δ ω) ξ - a

/-- **Lemma R.5 on one pocket test from its remaining clauses**: raw reference laws at level `0`, the base chart's
analytic data and `R5Clauses` give the phase side limit at `q`. -/
theorem pocketStopPhaseSideLimit_of_r5Clauses {Ω : Type*} {ℳ : ℕ → MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {C : Ω → Set ℂ} {F : ℕ → Ω → Set ℂ} {q : ℝ≥0} {δ : Ω → ℝ}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hpre : ∀ i, locPrefixSigma (ℳ i) A γ 0 ≤ mΩ)
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hFo : ∀ i ω, ω ∈ A → IsOpen (H \ F i ω))
    (hRawReference : ∀ i, PocketStopUnionLaw (ℳ i) P A γ C (F i) h₀ 0)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {ℓ : Ω → ℂ → ℂ}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    (hcInf : ∀ ω ∈ A, ∃ p : ℂ,
      Tendsto (fun w => mob ((c ω).2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p))
    (hKm : Measurable[mΩ, hittingSigma] (activeCompl A γ c q))
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {X : Ω → Set ℂ} {liftB : ℕ → Ω → ℂ → ℝ} {M : ℕ → Set Ω} {old : ℕ → Ω → Chart}
    (hcl : R5Clauses κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q) :
    PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u (activeCompl A γ c q) δ q := by
  obtain ⟨hX, hLattice, hOld, hLaw, hCover⟩ := hcl
  exact pocketStopPhaseSideLimit_of_incrementLaws_offExc hκ hh₀ hpre hCo hFo hRawReference hLattice hγ hc hcExt
    hcInf hKm hu hub hX hOld hLaw hCover

end InteractingSLE.Sec7.R5Phase
