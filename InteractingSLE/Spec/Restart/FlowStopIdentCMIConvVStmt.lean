/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIProofPath

/-!
# Measurable-exit successors for the explicit Cameron–Martin converse (R66)

The original premises are unchanged. The stopped coupling uses a measurable
version of the exit time which agrees with the raw exit almost surely.
`RLC.G3SourceStatement` itself requires only almost-sure agreement of paths;
it does not demand measurability of the raw exit time.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open StoppedExtend FlowStopIdentG

/-- R66 successor: CMIConverseVStatement uses a measurable exit version. -/
def CMIConverseVStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N →
    ∀ a c : ℝ, Icc a c ⊆ O → (∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c) →
      FlowStopIdentCM.shiftHullSet V a c ⊆ N →
    ∀ (F : CMCut) (q : ℂ → ℝ),
      IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q →
      (∀ z ∈ N, z ∈ H → F.f z = q z) → (∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) →
    ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
      (H₀ : S → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
    ∀ s : ℕ → TestOn upperHalfPlaneOpens, (∀ n z, |s n z| ≤ |F.src z|) →
      (∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))) →
    ∀ Λ : S → ℝ, Measurable Λ → (∀ᵐ x ∂Q₀, Tendsto (fun n => H₀ x (s n)) atTop (𝓝 (Λ x))) →
    ∀ k : ℝ, 0 < k → IsProbabilityMeasure (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))) →
    ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞) (h' : S → DistOn upperHalfPlaneOpens) (𝓕₀ : Filtration ℝ≥0 ‹_›)
      (W₀ : ℝ≥0 → S → ℝ) (VL₀ : Fin (flowLineNL b J y) → ℝ≥0 → S → ℝ)
      (VR₀ : Fin (flowLineNR b J y) → ℝ≥0 → S → ℝ) (B₀ : ℝ≥0 → S → ℝ),
      (∀ x, IsTranslateAddConst y (θ * QuantumZipper.chiC κ) (H₀ x) (h' x)) →
      IsOptionalHullCoupling κ (flowLineXL b J y) (flowLineXR b J y) (flowLineRhoL κ b J y θ)
        (flowLineRhoR κ b J y θ) Q₀ 𝓕₀ W₀ VL₀ VR₀ B₀ U h' →
      (∀ᵐ x ∂Q₀, IsGeneratingTrace (fun t => W₀ t x) (U x) (fun t => Γ x t - y)) →
      ∀ (hX : IsMeasurableKilledDriving W₀ VL₀ VR₀ U) (W₁ : ℝ≥0 → S → ℝ),
      (∀ τ : S → WithTop ℝ≥0, IsStoppingTime (drivingFiltration Q₀ hX) τ →
        (∀ᵐ ω ∂Q₀, (τ ω : ℝ≥0∞) < RLC.exitTime V (Γ ω) (U ω)) →
        ∀ᵐ ω ∂Q₀, StopPathData b J y N W₀ W₁ VL₀ VR₀ τ ω) →
      (∀ (τ : S → WithTop ℝ≥0) (hτ : IsStoppingTime (drivingFiltration Q₀ hX) τ),
        (∀ᵐ ω ∂Q₀, (τ ω : ℝ≥0∞) < RLC.exitTime V (Γ ω) (U ω)) →
        ∀ uR : S → ℂ → ℝ, (∀ ω, IsBoundedHarmonicExtension
          (forceBoundaryData κ (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ)
            (fun i => geomL (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXL bR Ĵ y i))
            (fun j => geomR (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXR bR Ĵ y j)))
          (forceJumpSet
            (fun i => geomL (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXL bR Ĵ y i))
            (fun j => geomR (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) (flowLineXR bR Ĵ y j)))
          (uR ω)) →
        ∀ φ : TestOn upperHalfPlaneOpens,
          ∀ᵐ ω ∂(Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))),
            Disjoint (tsupport φ) (fwdHull (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)) →
            (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x)))[fun ω' =>
                Complex.exp (Complex.I * ((h' ω' + chartShift F q y) φ : ℂ)) | hτ.measurableSpace] ω =
              LocalExt.cfVal (∫ z, couplingMean κ (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ)
                  (uR ω) z * φ z)
                (loewnerGreenEnergy (Ito.rpath (W₁ · ω)) (((τ ω).untopD 0 : ℝ≥0) : ℝ) φ)) →
      ∃ (e' : S → ℝ≥0∞), Measurable e' ∧
        (e' =ᵐ[Q₀] fun x => RLC.exitTime V (Γ x) (U x)) ∧
        ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
        IsStoppedFlowLine κ bR Ĵ y θ ((Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))).prod ν)
          (fun p => H₀ p.1 + smoothDist upperHalfPlaneOpens fun z => q z - F.f z) (fun p => Γ p.1)
          fun p => e' p.1

/-- R66 successor: CMIStoppedVStatement uses a measurable exit version. -/
def CMIStoppedVStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N →
    ∀ a c : ℝ, Icc a c ⊆ O → (∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c) → FlowStopIdentCM.shiftHullSet V a c ⊆ N →
    ∀ (F : CMCut) (q : ℂ → ℝ),
      IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q →
      (∀ z ∈ N, z ∈ H → F.f z = q z) → (∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) →
    ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
      (H₀ : S → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
    ∀ s : ℕ → TestOn upperHalfPlaneOpens, (∀ n z, |s n z| ≤ |F.src z|) →
      (∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))) →
    ∀ Λ : S → ℝ, Measurable Λ → (∀ᵐ x ∂Q₀, Tendsto (fun n => H₀ x (s n)) atTop (𝓝 (Λ x))) →
    ∀ k : ℝ, 0 < k → IsProbabilityMeasure (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))) →
    ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞), IsFlowLine κ b J y θ Q₀ H₀ Γ U →
      ∃ (e' : S → ℝ≥0∞), Measurable e' ∧
        (e' =ᵐ[Q₀] fun x => RLC.exitTime V (Γ x) (U x)) ∧
        ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
        IsStoppedFlowLine κ bR Ĵ y θ ((Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))).prod ν)
          (fun p => H₀ p.1 + smoothDist upperHalfPlaneOpens fun z => q z - F.f z) (fun p => Γ p.1)
          fun p => e' p.1

/-- R66 successor: FlowLineStopIdentCMIVStatement uses a measurable exit version. -/
def FlowLineStopIdentCMIVStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N →
    ∀ a c : ℝ, Icc a c ⊆ O → (∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c) → FlowStopIdentCM.shiftHullSet V a c ⊆ N →
    ∀ (F : CMCut) (q : ℂ → ℝ),
      IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q →
      (∀ z ∈ N, z ∈ H → F.f z = q z) → (∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) →
    ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ : Measure S) [IsProbabilityMeasure Q₀]
      (H₀ : S → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
    ∀ s : ℕ → TestOn upperHalfPlaneOpens, (∀ n z, |s n z| ≤ |F.src z|) →
      (∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))) →
    ∀ Λ : S → ℝ, Measurable Λ → (∀ᵐ x ∂Q₀, Tendsto (fun n => H₀ x (s n)) atTop (𝓝 (Λ x))) →
    ∀ k : ℝ, 0 < k → IsProbabilityMeasure (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))) →
    ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞), IsFlowLine κ b J y θ Q₀ H₀ Γ U →
      ∃ (e' : S → ℝ≥0∞), Measurable e' ∧
        (e' =ᵐ[Q₀] fun x => RLC.exitTime V (Γ x) (U x)) ∧
        ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
        IsStoppedFlowLineL κ bR Ĵ y θ V ((Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))).prod ν)
          (fun p => H₀ p.1 + smoothDist upperHalfPlaneOpens fun z => q z - F.f z) (fun p => Γ p.1)
          fun p => e' p.1

end InteractingSLE.Restart.FlowStopIdentCMI
