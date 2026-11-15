/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalLaw
import InteractingSLE.Spec.Supplement.SBS3MarkedPostReg

/-!
# S3: terminal physical labels for the original R51 history

Factor the selected post-stop word through the regularized retained record,
then evaluate the same measurable function on the original record. The
field stays fixed; equality of retained kernels transfers its law. Physical
labels transfer using equality of the actual runs at every finite stage.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- The original R51 history has a post-stop word carrying its exact-past
conditional GFF law and physical side labels, without a later launch. -/
theorem exists_postWord_interiorStageSides_reg {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      Measurable[pastSigma κ b jumps spec E (k + 1)] β ∧ Measurable Y ∧
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        min (instrTime spec k) (E k ω).2 ≠ ⊤ →
        (β ω).IsSorted ∧
        HasInteriorStageSides κ b jumps spec (fun j => E j ω) (k + 1) (β ω) ∧
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω)
          Y (β ω).fn (β ω).jumps) ∧
      ∃ (β₀ : Ω → BoundaryWord) (Y₀ : Ω → DistOn upperHalfPlaneOpens),
        IsStageWitness κ b jumps P h spec E k β₀ Y₀ ∧
        Y =ᵐ[P] (fun ω => recField κ
          (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)) (Y₀ ω)) := by
  obtain ⟨βr, Y, hβr, hY, hsort, hSide, β₀r, Y₀, hW, hField⟩ :=
    exists_postWord_interiorStageSides hκ hb hh (StagedReg.isStagedHistory_regHist hb hE hR)
      (WalkLaw.stagedPiecesRegular_regHist hR) StagedReg.isRegularDriver_regHist k
  obtain ⟨β₀, hW₀, -⟩ := exists_stageWitness_of_regHist hb hE hR hW
  rw [pastSigma_eq_comap] at hβr
  obtain ⟨f, hf, hfactor⟩ := hβr.exists_eq_measurable_comp
  let β : Ω → BoundaryWord := f ∘ pastMap κ b jumps spec E (k + 1)
  have hβ : Measurable[pastSigma κ b jumps spec E (k + 1)] β := by
    rw [pastSigma_eq_comap]
    exact hf.comp (comap_measurable _)
  have heq : β =ᵐ[P] βr := by
    filter_upwards [StagedReg.ae_pastMap_regHist hR (k + 1)] with ω hω
    rw [hfactor]
    exact congrArg f hω.symm
  have hm := measurable_pastMap (κ := κ) (E := StagedReg.regHist spec E) runMeasStatement hb spec
    (fun j _ => StagedReg.measurable_regHist (spec := spec) hE.1 j)
    (fun j _ ω => StagedReg.isRegularDriver_regHist (spec := spec) (E := E) j ω) (k + 1) le_rfl
  have hm₀ : Measurable (pastMap κ b jumps spec E (k + 1)) :=
    Measurable.of_comap_le (hE.2.1 (k + 1))
  have hK := StagedReg.ae_condExpKernel_eq_of_ae_eq hm hm₀
    (StagedReg.ae_pastMap_regHist hR (k + 1))
  refine ⟨β, Y, hβ, hY, ?_, β₀, Y₀, hW₀, ?_⟩
  · filter_upwards [hSide, heq, StagedReg.ae_run_regHist hR, hK]
      with ω hs hw hr hk hlaunch hfin
    have hlaunch' : (ExplState.run κ b jumps spec
        (fun j => StagedReg.regHist spec E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [hr (k + 1)]
      exact hlaunch
    have hfin' : min (instrTime spec k) (StagedReg.regHist spec E k ω).2 ≠ ⊤ := by
      simpa only [StagedReg.regHist_snd] using hfin
    obtain ⟨hphysical, hlaw⟩ := hs hlaunch' hfin'
    rw [hw]
    refine ⟨hsort ω, ?_, ?_⟩
    · intro y hy hyH
      have hyH' : LuM.bdVal (ExplState.run κ b jumps spec
          (fun j => StagedReg.regHist spec E j ω) (k + 1)).2.2.2.2.1 (y : ℂ) ∈ QuantumZipper.H := by
        rw [hr (k + 1)]
        exact hyH
      obtain ⟨j, hj, hjL, hjH⟩ := hphysical y hy hyH'
      rw [hr (j + 1)] at hjL
      exact ⟨j, hj, hjL, hjH⟩
    · rw [pastSigma_eq_comap, ← hk]
      exact hlaw
  · filter_upwards [hField, StagedReg.ae_pastMap_regHist hR (k + 1)] with ω hω hp
    rw [hω, hp]

end InteractingSLE.Theorem14.SB.S3
