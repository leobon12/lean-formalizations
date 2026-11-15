/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalMean
import InteractingSLE.Spec.Supplement.SBS3MarkedStage
import InteractingSLE.Spec.Supplement.SB2LcdKer

/-!
# S3: select the actual mean and physically labelled word together

The explored-set version and its local-set mean are constructed from marked
locality. A single stage witness supplies both the word's physical labels
and the identification of that actual mean. No comparison mean is assumed.
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

/-- Construct an actual explored-set mean and a conditional word with
physical side labels; every harmonic representative has this word's mean.
This version assumes regular drivers at every sample. -/
theorem exists_stageMean_interiorStageSides
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
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
  obtain ⟨hAvoid, hOpen, hMarked⟩ :=
    Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hE hreg hu₀ k
  let 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ} := ⟨pastSigma κ b jumps spec E k, hE.2.1 k⟩
  obtain ⟨A, hAm, hAc, hAeq, hAloc⟩ := Lcd.exists_lineVersion (P := P) 𝓜
    (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) hOpen hAvoid hMarked
  obtain ⟨g, hg, -⟩ := Lcd.exists_kernel_of_lineVersion 𝓜
    (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀) hAm hAc hAloc
  have hA : Measurable[mΩ, hittingSigma] A := hAm.mono 𝓜.2 le_rfl
  obtain ⟨β, Y, hW, hSide⟩ := exists_stageWitness_interiorStageSides hκ hb hh hE hR hreg k
  have hMean := ae_eqOn_stageMean_of_stageWitness h12p h13 hκ hκ4 hb hh hE hR hreg hW
    (hSide.mono fun _ hs hl => (hs hl).1) hu₀ hA hAeq hg
  refine ⟨A, g, β, Y, hA, hAc, hAeq, hg, hW, ?_⟩
  filter_upwards [hSide, hMean] with ω hs hm hl
  exact ⟨(hs hl).1, (hs hl).2, hm hl⟩

end InteractingSLE.Theorem14.SB.S3
