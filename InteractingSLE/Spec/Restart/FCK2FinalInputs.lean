/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2FinalCapacity

/-!
# The remaining finite-terminal collision input

The positive pre-lifetime collision checks are proved on the actual source
coupling. Only the finite endpoint implication is retained here as a named
unproved hypothesis; the capacity safe-law input remains separate.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)
namespace InteractingSLE.Restart.FCPlumb
open RetAux79 Sec7.PocketTraversal
universe u

/-- Exact finite-terminal assertion at one source chart path. -/
structure FCK2FinalTerminalInputs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (κ θ : ℝ) (d : PairData Ω) (β : Ω → BoundaryWord)
    (U : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) : Prop where
  terminal : ∀ a : ForceWordType, ∀ᵐ ω ∂P, ω ∈ fcTypeBranch κ θ (meetSet d) β a →
    ∀ T : ℝ≥0, (T : ℝ≥0∞) = U ω → ForceWord.ThresholdCondition a.rhoL a.rhoR (W T ω)
      (fun i => geomLW W (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) i T ω)
      (fun j => geomRW W (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) j T ω)

/-- Named missing finite-endpoint transfer, in the unchanged source context.
This definition does not assert that the terminal collision has been proved. -/
def FirstContactK2TerminalCollisionStatement : Prop :=
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
      ∀ (_hm₁ : ∀ t, Measurable (W₁ t)) (_hm₂ : ∀ t, Measurable (W₂ t)),
      (∀ ω, Continuous (W₁ · ω)) → (∀ ω, Continuous (W₂ · ω)) →
      (∀ ω, W₁ 0 ω = 0) → (∀ ω, W₂ 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
        IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) →
      FCK2FinalTerminalInputs P κ θ₁ d β U₁ W₁ ∧
        FCK2FinalTerminalInputs P κ θ₂ d β U₂ W₂

end InteractingSLE.Restart.FCPlumb
