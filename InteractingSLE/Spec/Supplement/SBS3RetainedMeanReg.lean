/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3RetainedMean

/-!
# S3: actual finite-prefix means under exactly R51
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart LocalSets

/-- The actual explored set, actual local mean and physically labelled
conditional word at every finite prefix of the original R51 history.
The mean identity holds for every harmonic representative on one conull
event, with no launch condition. -/
theorem exists_retainedMean_reg
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (k : ℕ) (htime : HasFiniteOrdinaryTimes spec k) :
    ∃ (A : Ω → Set ℂ) (g : Ω → DistOn upperHalfPlaneOpens)
        (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      Measurable[mΩ, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      (∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps spec E k ω) ∧
      IsLocalSetMean A (WholeField.centredField h u₀) P g ∧
      RetainedWordWitness κ b jumps P h spec E k β Y ∧
      ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
          g ω φ = ∫ z, v z * φ z) →
        EqOn (fun z => v z + u₀ z + chiC κ *
            (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2 z)
          (fun z => (β ω).mean ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 z))
          (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.dom := by
  obtain ⟨A, g, βr, Y, hAm, hAc, hAeq, hg, hWr, hMean⟩ :=
    exists_retainedMean h12p h13 hκ hκ4 hb hh
      (StagedReg.isStagedHistory_regHist hb hE hR) (WalkLaw.stagedPiecesRegular_regHist hR)
      StagedReg.isRegularDriver_regHist hu₀ k htime
  obtain ⟨β, hW, heq⟩ := exists_retainedWordWitness_of_regHist hb hE hR hWr
  refine ⟨A, g, β, Y, hAm, hAc, ?_, hg, hW, ?_⟩
  · filter_upwards [hAeq, StagedReg.ae_run_regHist hR] with ω ha hr
    rw [ha]
    unfold WalkLaw.stageSet
    rw [hr k]
  · filter_upwards [hMean, heq, StagedReg.ae_run_regHist hR] with ω hm hw hr v hv hrep
    have he := hm v hv hrep
    rw [hr k] at he
    rw [hw]
    exact he

end InteractingSLE.Theorem14.SB.S3
