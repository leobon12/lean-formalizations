/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2BdryCapacity
import InteractingSLE.Spec.Restart.FCK2BdrySourceSeed

/-!
# Exact remaining capacity and boundary inputs

Collapsed-side seeds have been discharged. The two named statements below
record the remaining mathematical inputs, without asserting either one.
The capacity exhaustion lemmas in `FCK2BdryCapacity` are available for a
construction from increasing observed windows.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open RetAux79 DomainMarkov.K2 Sec7.PocketTraversal
universe u
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Conditional Gaussian and complement identities for the actual capacity
filtration. No threshold identity or seed inequality is a field. -/
structure FCK2BdrySafeInputs (P : Measure Ω) (κ θ : ℝ) (d : PairData Ω)
    (β : Ω → BoundaryWord) (Hc : Ω → DistOn upperHalfPlaneOpens)
    (U : Ω → ℝ≥0∞) (_γ : Ω → ℝ≥0 → ℂ) (W : ℝ≥0 → Ω → ℝ)
    (𝓕 : Filtration ℝ≥0 mΩ) : Prop where
  safe_law : ∀ a : ForceWordType,
    HasSafeLaw κ a.rhoL a.rhoR P 𝓕 (fcTypeBranch κ θ (meetSet d) β a) U W
      (geomLW W (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω)))
      (geomRW W (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)))
      (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω))
  safe_members : HasSafeMembers P 𝓕 (meetSet d) U W
    (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω))

/-- The positive noninterior and terminal collision checks. These are the
remaining geometric weight comparisons; interior collisions are excluded by
`RetPlumbProofFinalCollision`. -/
structure FCK2BdryCollisionInputs (P : Measure Ω) (κ θ : ℝ) (d : PairData Ω)
    (β : Ω → BoundaryWord) (Hc : Ω → DistOn upperHalfPlaneOpens)
    (U : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ) (W : ℝ≥0 → Ω → ℝ)
    (_𝓕 : Filtration ℝ≥0 mΩ) : Prop where
  boundary : ∀ a : ForceWordType, ∀ᵐ ω ∂P, ω ∈ fcTypeBranch κ θ (meetSet d) β a →
    ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < U ω → γ ω t ∉ QuantumZipper.H →
      ¬ ForceWord.ThresholdCondition a.rhoL a.rhoR (W t ω)
        (fun i => geomLW W (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) i t ω)
        (fun j => geomRW W (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) j t ω)
  terminal : ∀ a : ForceWordType, ∀ᵐ ω ∂P, ω ∈ fcTypeBranch κ θ (meetSet d) β a →
    ∀ T : ℝ≥0, (T : ℝ≥0∞) = U ω → ForceWord.ThresholdCondition a.rhoL a.rhoR (W T ω)
      (fun i => geomLW W (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) i T ω)
      (fun j => geomRW W (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) j T ω)

/-- Named missing input: source conditional laws after passage from retained
physical histories to the canonical capacity filtration. Ordinary R1 does
not apply directly on the first-contact lines, which already meet. -/
def FirstContactK2CapacitySafeLawsStatement : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [_mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : PairData Ω) (hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord, Measurable[retSigma d P] β →
      (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) →
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞),
      (∀ t, Measurable fun ω => γ₁ ω t) → (∀ t, Measurable fun ω => γ₂ ω t) →
      Measurable U₁ → Measurable U₂ → d.IsCanonClock P γ₁ γ₂ U₁ U₂ →
    ∀ W₁ W₂ : ℝ≥0 → Ω → ℝ,
      ∀ (hm₁ : ∀ t, Measurable (W₁ t)) (hm₂ : ∀ t, Measurable (W₂ t)),
      (∀ ω, Continuous (W₁ · ω)) → (∀ ω, Continuous (W₂ · ω)) →
      (∀ ω, W₁ 0 ω = 0) → (∀ ω, W₂ 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
        IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) →
      (FCK2BdrySafeInputs P κ θ₁ d β (hd.chartField κ h) U₁ γ₁ W₁
        (fcRetainedDriverFiltration P hd W₁ hm₁)) ∧
        (FCK2BdrySafeInputs P κ θ₂ d β (hd.chartField κ h) U₂ γ₂ W₂
          (fcRetainedDriverFiltration P hd W₂ hm₂))

/-- Named missing input: the real-boundary and finite-endpoint collision
weight comparisons for each canonical chart path. No source theorem is
replaced by this conditional interface. -/
def FirstContactK2BoundaryCollisionStatement : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [_mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : PairData Ω) (hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord, Measurable[retSigma d P] β →
      (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) →
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞),
      (∀ t, Measurable fun ω => γ₁ ω t) → (∀ t, Measurable fun ω => γ₂ ω t) →
      Measurable U₁ → Measurable U₂ → d.IsCanonClock P γ₁ γ₂ U₁ U₂ →
    ∀ W₁ W₂ : ℝ≥0 → Ω → ℝ,
      ∀ (hm₁ : ∀ t, Measurable (W₁ t)) (hm₂ : ∀ t, Measurable (W₂ t)),
      (∀ ω, Continuous (W₁ · ω)) → (∀ ω, Continuous (W₂ · ω)) →
      (∀ ω, W₁ 0 ω = 0) → (∀ ω, W₂ 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
        IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) →
      (FCK2BdryCollisionInputs P κ θ₁ d β (hd.chartField κ h) U₁ γ₁ W₁
        (fcRetainedDriverFiltration P hd W₁ hm₁)) ∧
        (FCK2BdryCollisionInputs P κ θ₂ d β (hd.chartField κ h) U₂ γ₂ W₂
          (fcRetainedDriverFiltration P hd W₂ hm₂))

end InteractingSLE.Restart.FCPlumb
