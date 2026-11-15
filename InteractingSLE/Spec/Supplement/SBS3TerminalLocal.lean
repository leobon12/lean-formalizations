/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalSelectReg

/-!
# S3: local-set inputs for actual R51 stage versions

A measurable version of the actual explored set is local, determined by
the field up to null sets, and has only unbounded lower-union components.
The proof regularizes only the history used to establish marked locality;
all three conclusions concern the supplied version of the original set.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart LocalSets

/-- A measurable actual-stage version satisfies all local-set, field
determination and lower-component inputs of the protected union comparison,
under exactly R51. -/
theorem stageSet_version_local_determined
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (k : ℕ)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAeq : ∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps spec E k ω) :
    IsLocalSet A (WholeField.centredField h u₀) P ∧
      MeasurableSpace.comap A hittingSigma ≤
        aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P ∧
      ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
        ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z) := by
  have hEr := StagedReg.isStagedHistory_regHist hb hE hR
  have hRr := WalkLaw.stagedPiecesRegular_regHist hR
  obtain ⟨hAvoid, -, hMarked⟩ := Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh
    hEr StagedReg.isRegularDriver_regHist hu₀ k
  have hAreg : ∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps spec (StagedReg.regHist spec E) k ω := by
    filter_upwards [hAeq, StagedReg.ae_run_regHist hR] with ω ha hr
    rw [ha]
    unfold WalkLaw.stageSet
    rw [hr k]
  have hMarkA := WalkLaw.isHistoryAvoidanceLocal_congr_ae (hAreg.mono fun _ he => he.symm) hMarked
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [hAeq, WalkLaw.ae_isOpen_H_diff_stageSet hR k] with ω he ho
    rw [he]
    exact ⟨WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω, ho⟩
  have hLocal : IsLocalSet A (WholeField.centredField h u₀) P :=
    ((isLocalSet_tfae (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀) hA hAc).out 4 1).2
      hMarkA.isAvoidanceLocal
  have hAJ := WalkBdry.hitting_comap_le_aeSigma (WalkBdry.avoid_aeSigma_congr hAreg hAvoid)
  obtain ⟨f, hfm, hfe⟩ := StagedDet.exists_pastMap_eq_comp_field h12p h13 hκ hκ4 hb hh hEr hRr k
  have hdet := WalkLaw.pastSigma_le_aeSigma_centred hfm hfe u₀
  refine ⟨hLocal, ?_, ?_⟩
  · intro G hG
    obtain ⟨G', hG', he⟩ := hAJ G hG
    obtain ⟨G'', hG'', he'⟩ := hdet G' hG'
    exact ⟨G'', hG'', he.trans he'⟩
  · filter_upwards [hAeq, hR.ae_pieceRegular] with ω ha hr
    rw [ha]
    exact WalkSide.not_isBounded_lowerUnion_stageSet spec E ω hr k

end InteractingSLE.Theorem14.SB.S3
