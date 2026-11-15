/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalSelect

/-!
# S3: the physical word and actual mean under exactly R51

Pass the selected mean and field unchanged from the regularized history to
the original one. The word is factored back through the original retained
past. Equality of runs transfers both its physical labels and the formula
for every harmonic representative of the actual explored-set mean.
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

/-- An actual explored-set mean and a physically labelled word with its
original-past conditional GFF law, under only R51 piece regularity. -/
theorem exists_stageMean_interiorStageSides_reg
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (k : ℕ) :
    ∃ (A : Ω → Set ℂ) (g : Ω → DistOn upperHalfPlaneOpens)
        (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      Measurable[mΩ, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      (∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps spec E k ω) ∧
      IsLocalSetMean A (WholeField.centredField h u₀) P g ∧
      IsStageWitness κ b jumps P h spec E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        (β ω).IsSorted ∧ HasInteriorStageSides κ b jumps spec (fun j => E j ω) k (β ω) ∧
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
            g ω φ = ∫ z, v z * φ z) →
          EqOn (fun z => v z + u₀ z + chiC κ *
              (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2 z)
            (fun z => (β ω).mean ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 z))
            (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.dom := by
  obtain ⟨A, g, βr, Y, hAm, hAc, hAeq, hg, hWr, hSides⟩ :=
    exists_stageMean_interiorStageSides h12p h13 hκ hκ4 hb hh
      (StagedReg.isStagedHistory_regHist hb hE hR) (WalkLaw.stagedPiecesRegular_regHist hR)
      StagedReg.isRegularDriver_regHist hu₀ k
  obtain ⟨β, hW, hβeq⟩ := exists_stageWitness_of_regHist hb hE hR hWr
  refine ⟨A, g, β, Y, hAm, hAc, ?_, hg, hW, ?_⟩
  · filter_upwards [hAeq, StagedReg.ae_run_regHist hR] with ω ha hr
    rw [ha]
    unfold WalkLaw.stageSet
    rw [hr k]
  · filter_upwards [hSides, hβeq, StagedReg.ae_run_regHist hR] with ω hs hw hr hlaunch
    have hlaunch' : (ExplState.run κ b jumps spec
        (fun j => StagedReg.regHist spec E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [hr (k + 1)]
      exact hlaunch
    obtain ⟨hsort, hphysical, hmean⟩ := hs hlaunch'
    rw [hw]
    refine ⟨hsort, ?_, ?_⟩
    · intro y hy hyH
      have hyH' : LuM.bdVal (ExplState.run κ b jumps spec
          (fun j => StagedReg.regHist spec E j ω) k).2.2.2.2.1 (y : ℂ) ∈ H := by
        rw [hr k]
        exact hyH
      obtain ⟨j, hj, hjL, hjH⟩ := hphysical y hy hyH'
      rw [hr (j + 1)] at hjL
      exact ⟨j, hj, hjL, hjH⟩
    · intro v hv hrep
      have he := hmean v hv hrep
      rw [hr k] at he
      exact he

end InteractingSLE.Theorem14.SB.S3
