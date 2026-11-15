/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedPost

/-!
# S3: finite post-stop words for the original R51 history

Retain the exact original past sigma algebra when passing back from the
regularized history. The post field is linked to the original stage field
and record, including when the stop is terminal.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- The original history has a sorted post-stop word with its numerical
genealogy, full retained-past GFF law and actual field provenance under R51.
No later launch and no every-sample regularity assumption are required. -/
theorem exists_postWord_heightOrigin_reg {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      Measurable[pastSigma κ b jumps spec E (k + 1)] β ∧ Measurable Y ∧
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        (β ω).IsSorted ∧
        (∀ y ∉ (β ω).jumps,
          StageHeight κ b jumps spec (fun j => E j ω) (k + 1) ((β ω).fn y)) ∧
        (min (instrTime spec k) (E k ω).2 ≠ ⊤ →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω)
            Y (β ω).fn (β ω).jumps)) ∧
      ∃ (β₀ : Ω → BoundaryWord) (Y₀ : Ω → DistOn upperHalfPlaneOpens),
        IsStageWitness κ b jumps P h spec E k β₀ Y₀ ∧
        Y =ᵐ[P] (fun ω => recField κ
          (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)) (Y₀ ω)) := by
  obtain ⟨βr, Y, hβr, hY, hsort, hOrigin, hLaw, β₀r, Y₀, hW, hField⟩ :=
    exists_postWord_heightOrigin hκ hb hh (StagedReg.isStagedHistory_regHist hb hE hR)
      StagedReg.isRegularDriver_regHist k
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
  · filter_upwards [hOrigin, hLaw, heq, StagedReg.ae_run_regHist hR, hK]
      with ω ho hl hw hr hk hlaunch
    have hlaunch' : (ExplState.run κ b jumps spec
        (fun j => StagedReg.regHist spec E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [hr (k + 1)]; exact hlaunch
    rw [hw]
    refine ⟨hsort ω, ?_, ?_⟩
    · intro y hy
      rcases ho hlaunch' y hy with hOrig | ⟨j, hj, hjL, hjH⟩
      · exact Or.inl hOrig
      · rw [hr (j + 1)] at hjL
        exact Or.inr ⟨j, hj, hjL, hjH⟩
    · intro hfin
      rw [pastSigma_eq_comap, ← hk]
      apply hl hlaunch'
      simpa only [StagedReg.regHist_snd] using hfin
  · filter_upwards [hField, StagedReg.ae_pastMap_regHist hR (k + 1)] with ω hω hp
    rw [hω, hp]

/-- The post field is the original field read in the composed physical
chart, on every launched instruction. This uses the inherited chain-rule
lift and the actual last retained record. -/
theorem ae_postTransport_of_stageWitness {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    {β : Ω → BoundaryWord} {Y Z : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y)
    (hZ : Z =ᵐ[P] (fun ω => recField κ
      (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)) (Y ω))) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsChartTransport
        ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.trans
          (recChart (pastMap κ b jumps spec E (k + 1) ω (Fin.last k))))
        1 0 (QuantumZipper.chiC κ) (h ω) (Z ω) := by
  filter_upwards [hW.2.2.1, hZ] with ω hω hz hlaunch
  obtain ⟨hc, hlift, ht⟩ := hω hlaunch
  rw [hz]
  exact IsChartTransport.trans hc (isConformal_recChart _) hlift (continuousOn_recChart_lift _) ht
    (isChartTransport_recField κ _ _)

end InteractingSLE.Theorem14.SB.S3
