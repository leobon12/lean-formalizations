/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRefLaws
import InteractingSLE.Spec.Sec7.PocketSideInRefPhase

/-!
# Phase side limits from incident reference germs

PROVE-POCKET-SIDEIN, R73 §3.1. Choose actual reference means from their own raw
stopped laws, then transfer their limits in the incident chart. `hCollar` is the
exact remaining R.5 comparison, not an assumption about a whole physical ball
or equality of complete conditional means. The same phase occurs on every face.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal Lemma71C PocketStop PocketStopField
  PocketUnionPt PocketCoupling Aux119Heights PhaseSel

/-- Raw laws provide the reference means. The named incident-chart comparison
keeps the unfinished collar and exact inherited heights visible in the type. -/
theorem pocketStopPhaseSideLimit_of_raw_reference_germs {Ω ι : Type*}
    {ℳ : ι → MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {C K : Ω → Set ℂ} {F : ι → Ω → Set ℂ} {q q₀ : ℝ≥0} {δ : Ω → ℝ}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hpre : ∀ i, locPrefixSigma (ℳ i) A γ q₀ ≤ mΩ)
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hFo : ∀ i ω, ω ∈ A → IsOpen (H \ F i ω))
    (hRawReference : ∀ i, PocketStopUnionLaw (ℳ i) P A γ C (F i) h₀ q₀)
    {liftB : ι → Ω → ℂ → ℝ}
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hCollar : ∀ gB : ι → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A γ C (F i) q₀) h₀ P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h₀ P g →
      ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ K ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ K ω →
            g ω φ = ∫ z, v z * φ z) →
          ∀ ξ : ℝ, ξ ∉ forceJumpSet
            (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
            (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
            ∃ (i : ι) (b d : ℝ),
              let inv := (relChart c γ q ω).2.1;
              let vB := harmRep (gB i ω) (H \ liveExt A γ C (F i) q₀ ω);
              Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
              Tendsto (fun y => vB (inv y) + u (inv y) + chiC κ * liftB i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
              Tendsto (fun y => (relChart c γ q ω).2.2 (inv y) - liftB i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
              b + chiC κ * d = phaseData κ ρL ρR
                (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
                (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)
                (δ ω) ξ - a) :
    PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u K δ q := by
  classical
  have hMeans : ∀ i, ∃ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (liveExt A γ C (F i) q₀) h₀ P g := fun i =>
    (referenceFacts_of_unionLaw hh₀ (hpre i) hCo (hFo i) (hRawReference i)).2.2
  choose gB hgB using hMeans
  refine ⟨hLattice, fun g hg => ?_⟩
  filter_upwards [hCollar gB hgB g hg] with ω hω hA hq v hv hvr ξ hξ
  obtain ⟨i, b, d, hdiff, hheight, hlift, hword⟩ := hω hA hq v hv hvr ξ hξ
  have hsum := hdiff.add (hheight.add (hlift.const_mul (chiC κ)))
  rw [zero_add, hword] at hsum
  exact hsum.congr fun y => by
    ring

end InteractingSLE.Sec7.PocketStopSide
