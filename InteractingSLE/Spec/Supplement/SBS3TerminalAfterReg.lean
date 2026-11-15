/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalAfterMean

/-!
# S3: the terminal physical word and actual mean under R51

The original history's post-stop past, field law, explored set and physical
chart are retained exactly. Only the auxiliary proof is performed with
regularized drivers; no every-sample regularity premise remains.
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

/-- An actual mean and physically labelled conditional word after a finite
stop of the original R51 history. A later launch is not assumed. -/
theorem exists_postMean_interiorStageSides_reg
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
      (∀ᵐ ω ∂P, A ω = WalkLaw.stageSet κ b jumps spec E (k + 1) ω) ∧
      IsLocalSetMean A (WholeField.centredField h u₀) P g ∧
      Measurable[pastSigma κ b jumps spec E (k + 1)] β ∧ Measurable Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        min (instrTime spec k) (E k ω).2 ≠ ⊤ →
        (β ω).IsSorted ∧ HasInteriorStageSides κ b jumps spec (fun j => E j ω) (k + 1) (β ω) ∧
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω)
          Y (β ω).fn (β ω).jumps ∧
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
            g ω φ = ∫ z, v z * φ z) →
          EqOn (fun z => v z + u₀ z + chiC κ *
              (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.2.2 z)
            (fun z => (β ω).mean ((ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.1 z))
            (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.dom := by
  obtain ⟨A, g, βr, Y, hAm, hAc, hAeq, hg, hβr, hY, hSides⟩ :=
    exists_postMean_interiorStageSides h12p h13 hκ hκ4 hb hh
      (StagedReg.isStagedHistory_regHist hb hE hR) (WalkLaw.stagedPiecesRegular_regHist hR)
      StagedReg.isRegularDriver_regHist hu₀ k
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
  refine ⟨A, g, β, Y, hAm, hAc, ?_, hg, hβ, hY, ?_⟩
  · filter_upwards [hAeq, StagedReg.ae_run_regHist hR] with ω ha hr
    rw [ha]
    unfold WalkLaw.stageSet
    rw [hr (k + 1)]
  · filter_upwards [hSides, heq, StagedReg.ae_run_regHist hR, hK] with ω hs hw hr hk hlaunch hfin
    have hlaunch' : (ExplState.run κ b jumps spec
        (fun j => StagedReg.regHist spec E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [hr (k + 1)]
      exact hlaunch
    have hfin' : min (instrTime spec k) (StagedReg.regHist spec E k ω).2 ≠ ⊤ := by
      simpa only [StagedReg.regHist_snd] using hfin
    obtain ⟨hsort, hphysical, hlaw, hmean⟩ := hs hlaunch' hfin'
    rw [hw]
    refine ⟨hsort, ?_, ?_, ?_⟩
    · intro y hy hyH
      have hyH' : LuM.bdVal (ExplState.run κ b jumps spec
          (fun j => StagedReg.regHist spec E j ω) (k + 1)).2.2.2.2.1 (y : ℂ) ∈ H := by
        rw [hr (k + 1)]
        exact hyH
      obtain ⟨j, hj, hjL, hjH⟩ := hphysical y hy hyH'
      rw [hr (j + 1)] at hjL
      exact ⟨j, hj, hjL, hjH⟩
    · rw [pastSigma_eq_comap, ← hk]
      exact hlaw
    · intro v hv hrep
      have he := hmean v hv hrep
      rw [hr (k + 1)] at he
      exact he

end InteractingSLE.Theorem14.SB.S3
