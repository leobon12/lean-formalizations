/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRefGerm
import InteractingSLE.Spec.Sec7.PocketSideInRefJoint

/-!
# The R73 reference-germ route to canonical pocket side limits

PROVE-POCKET-SIDEIN. Raw stopped laws provide reference means, R.5's incident
comparison transfers their phase word, the bounded-horizon mean probes give
phase continuity, and joint R.6 candidate germs anchor phase zero. The output
is the unchanged all-q side-limit predicate. The exact remaining source
constructions are `hRawReference`, `hLattice`, `hCollar`, `hProbes`,
`hJointGerms`, `hVisits`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal Lemma71C PocketStop PocketStopField
  PocketUnionPt PocketCoupling Aux119Heights PhaseSel

/-- Canonical side limits from raw reference laws and the exact R73 collar,
finite-mean and shared-side data. No phase-limit, phase-continuity or zero-visit
conclusion is assumed. The named source constructions remain conditional. -/
theorem pocketStopSideLimit_of_reference_germs_probes {Ω ι ν : Type*} {ℳ : ν → MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [Countable ι] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 4 < κ)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {K : ℝ≥0 → Ω → Set ℂ} {δ : ℝ≥0 → Ω → ℝ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hseedR : ∀ ω ∈ A, xR ω 0 = 0)
    {C : Ω → Set ℂ} {F : ν → Ω → Set ℂ} {q₀ : ℝ≥0}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hpre : ∀ i, locPrefixSigma (ℳ i) A γ q₀ ≤ mΩ)
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hFo : ∀ i ω, ω ∈ A → IsOpen (H \ F i ω))
    (hRawReference : ∀ i, PocketStopUnionLaw (ℳ i) P A γ C (F i) h₀ q₀)
    {liftB : ν → Ω → ℂ → ℝ}
    (hLattice : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∃ m : ℤ, δ q ω = m * phaseStep κ)
    (hCollar : ∀ q : ℝ≥0, ∀ gB : ν → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A γ C (F i) q₀) h₀ P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (K q) h₀ P g →
      ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ K q ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ K q ω →
            g ω φ = ∫ z, v z * φ z) →
          ∀ ξ : ℝ, ξ ∉ forceJumpSet
            (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
            (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
            ∃ (i : ν) (b d : ℝ),
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
                (δ q ω) ξ - a)
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
    ∀ q, PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u (K q) q := by
  apply pocketStopSideLimit_of_phase_probes_joint_germs hκ hγ hseedL hseedR
    (fun q => pocketStopPhaseSideLimit_of_raw_reference_germs hh₀ hpre hCo hFo
      hRawReference (hLattice q) (hCollar q)) hProbes hJointGerms hVisits

end InteractingSLE.Sec7.PocketStopSide
