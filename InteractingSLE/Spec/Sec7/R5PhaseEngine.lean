/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux29CorSide

/-!
# Lemma R.5 for one pocket test: the phase side limit from old-chart increment laws and a cover

Packet PROVE-R5-PHASE. Specification §5.5 (`source/spec/p433-480.md` L1003–L1022, pp. 474–475): Lemma R.5 and the
corollary "the full stopped Gaussian kernel". The source's argument at a relative capacity `q` has three parts:

1. **old references** — for each original rational time `s`, the marked union law of the pocket exterior with the
   counterflow hull at `s` (a raw stopped law; its local-set mean `g_s` is the reference mean);
2. **the nested law** — on the event that `s` is an earlier visit, the increment from the reference to the current
   relative stop is a local set of a zero-boundary field in the reference chart (an old-chart increment law), so the
   current mean has the reference's boundary germ wherever the increment avoids an incident half-disc
   (zero-boundary decay);
3. **the cover** — every real current coordinate whose physical landing is not one of finitely many exceptional
   points (the attachments, the current tip, the pocket target) has an unfilled incident half-disc in some reference
   chart, at which the reference has an exact height and the two lifts have a limiting difference; these combine into
   the phase-shifted word. Aux. 29 removes the exceptional prime ends.

`pocketStopPhaseSideLimit_of_incrementLaws_offExc` composes the two landed generic steps
(`PocketStopSide.collar_of_oldChartIncrementLaws` for 2, `Aux29Cor.pocketStopPhaseSideLimit_of_collar_offExc` for
3's Aux. 29 part): it holds for **every** pocket test, every word, every margin, with no hypothesis about the R.7
configuration. Conditional helper with a distinct name; nothing here uses Theorem 1.2/1.3 (R43, R48).
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

/-- **Lemma R.5 on one pocket test at one relative capacity** (generic in the word and the test): raw reference
laws at a fixed relative level `q₀`, the base chart's analytic data, a lattice-valued phase `δ`, reference charts on
pair events `M i`, the old-chart increment laws, and the cover off a finite exceptional physical set `X` give the
phase side limit at `q`. -/
theorem pocketStopPhaseSideLimit_of_incrementLaws_offExc {Ω ι : Type*} [Countable ι]
    {ℳ : ι → MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {C : Ω → Set ℂ} {F : ι → Ω → Set ℂ} {q q₀ : ℝ≥0} {δ : Ω → ℝ}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hpre : ∀ i, locPrefixSigma (ℳ i) A γ q₀ ≤ mΩ)
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hFo : ∀ i ω, ω ∈ A → IsOpen (H \ F i ω))
    (hRawReference : ∀ i, PocketStopUnionLaw (ℳ i) P A γ C (F i) h₀ q₀)
    {liftB : ι → Ω → ℂ → ℝ}
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {ℓ : Ω → ℂ → ℂ}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    (hcInf : ∀ ω ∈ A, ∃ p : ℂ,
      Tendsto (fun w => mob ((c ω).2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p))
    (hKm : Measurable[mΩ, hittingSigma] (activeCompl A γ c q))
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {X : Ω → Set ℂ} (hX : ∀ ω, (X ω).Finite)
    {M : ι → Set Ω} {old : ι → Ω → Chart}
    (hOld : ∀ i, ∀ ω ∈ M i, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧ (old i ω).IsConformal ∧
      ((relChart c γ q ω).dom : Set ℂ) ⊆ (old i ω).dom ∧
      ((old i ω).dom : Set ℂ) = H \ liveExt A γ C (F i) q₀ ω)
    (hLaw : ∀ gB : ι → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A γ C (F i) q₀) h₀ P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
      ∀ i, HasOldChartIncrementLaw P (M i) (old i) (relChart c γ q) (gB i) g)
    (hCover : ∀ gB : ι → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A γ C (F i) q₀) h₀ P (gB i)) →
      ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
        extendFrom H (relChart c γ q ω).2.1 ξ ∉ X ω →
        ∃ (i : ι) (x r b d : ℝ), ω ∈ M i ∧ 0 < r ∧
          (old i ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (relChart c γ q ω).dom ∧
          Tendsto (fun z => (old i ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          Tendsto (fun y => harmRep (gB i ω) (H \ liveExt A γ C (F i) q₀ ω) ((relChart c γ q ω).2.1 y) +
              u ((relChart c γ q ω).2.1 y) + chiC κ * liftB i ω ((relChart c γ q ω).2.1 y))
            (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
          Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
              liftB i ω ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
          b + chiC κ * d = phaseData κ ρL ρR
            (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
            (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)
            (δ ω) ξ - a) :
    PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u (activeCompl A γ c q) δ q := by
  classical
  refine pocketStopPhaseSideLimit_of_collar_offExc (liftB := liftB) hκ hh₀ hpre hCo hFo hRawReference hLattice hγ
    hc hcExt hcInf hKm hu hub hX ?_
  intro gB hgB g hg
  have hcol := collar_of_oldChartIncrementLaws (P := P) (A := A) (γ := γ) (c := c) (q := q) (h₀ := h₀) (u := u)
    (k := chiC κ) (B := fun i => liveExt A γ C (F i) q₀) (liftB := liftB)
    (J := fun ω => {ξ : ℝ | ξ ∈ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
      (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) ∨
      extendFrom H (relChart c γ q ω).2.1 ξ ∈ X ω})
    (Wd := fun ω ξ => phaseData κ ρL ρR
      (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
      (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) (δ ω) ξ - a)
    (M := M) (old := old) hγ (fun ω hω => (hc ω hω).1) hOld hLaw ?_ gB hgB g hg
  · filter_upwards [hcol] with ω hω hωA hq v hv hvr ξ hξ hξX
    exact hω hωA hq v hv hvr ξ (fun h => h.elim hξ hξX)
  · intro gB' hgB'
    filter_upwards [hCover gB' hgB'] with ω hω hωA hq ξ hξ
    exact hω hωA hq ξ (fun h => hξ (Or.inl h)) (fun h => hξ (Or.inr h))

end InteractingSLE.Sec7.R5Phase
