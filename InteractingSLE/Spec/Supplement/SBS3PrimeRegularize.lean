/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3PrimeSchedule
import InteractingSLE.Spec.Supplement.StagedRegularize

/-!
# S3: actual stage words under R51's almost-sure regularity hypothesis

Transport a conditional-law witness from the regularized history back to the
original history. Factor its word through the retained past before changing
versions, so the resulting word is measurable for the original past exactly.
The genealogy then applies with `StagedPiecesRegular`, without an additional
every-sample regularity assumption.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- Transfer a regularized stage witness to the original retained sigma
algebra, with the same field and an almost surely equal word. -/
theorem exists_stageWitness_of_regHist {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) {k : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec (StagedReg.regHist spec E) k β Y) :
    ∃ β₀ : Ω → BoundaryWord, IsStageWitness κ b jumps P h spec E k β₀ Y ∧ β₀ =ᵐ[P] β := by
  have hβ := hW.1
  rw [pastSigma_eq_comap] at hβ
  obtain ⟨f, hf, hfactor⟩ := hβ.exists_eq_measurable_comp
  let β₀ : Ω → BoundaryWord := f ∘ pastMap κ b jumps spec E k
  have hβ₀ : Measurable[pastSigma κ b jumps spec E k] β₀ := by
    rw [pastSigma_eq_comap]
    exact hf.comp (comap_measurable _)
  have heq : β₀ =ᵐ[P] β := by
    filter_upwards [StagedReg.ae_pastMap_regHist hR k] with ω hω
    rw [hfactor]
    exact congrArg f hω.symm
  have hm : Measurable (pastMap κ b jumps spec (StagedReg.regHist spec E) k) :=
    measurable_pastMap runMeasStatement hb spec
      (fun j _ => StagedReg.measurable_regHist hE.1 j)
      (fun j _ ω => StagedReg.isRegularDriver_regHist j ω) k le_rfl
  have hm₀ : Measurable (pastMap κ b jumps spec E k) := Measurable.of_comap_le (hE.2.1 k)
  have hK := StagedReg.ae_condExpKernel_eq_of_ae_eq hm hm₀ (StagedReg.ae_pastMap_regHist hR k)
  refine ⟨β₀, ⟨hβ₀, hW.2.1, ?_, ?_⟩, heq⟩
  · filter_upwards [hW.2.2.1, StagedReg.ae_run_regHist hR] with ω hω hrun hlaunch
    have hlaunch' : (ExplState.run κ b jumps spec
        (fun j => StagedReg.regHist spec E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [hrun (k + 1)]
      exact hlaunch
    have hpath := hω hlaunch'
    rw [hrun k] at hpath
    exact hpath
  · filter_upwards [hW.2.2.2, hK, StagedReg.ae_run_regHist hR, heq]
      with ω₀ hω hker hrun hword hlaunch
    have hlaunch' : (ExplState.run κ b jumps spec
        (fun j => StagedReg.regHist spec E j ω₀) (k + 1)).2.2.2.1 k ≠ none := by
      rw [hrun (k + 1)]
      exact hlaunch
    rw [hword, pastSigma_eq_comap, ← hker]
    exact hω hlaunch'

/-- The actual stage-word genealogy under precisely R51's regularity
hypothesis. The witness is for the original history and original past. -/
theorem exists_stageWitness_heightOrigin_reg {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        ∀ y ∉ (β ω).jumps,
          StageHeight κ b jumps spec (fun j => E j ω) k ((β ω).fn y) := by
  obtain ⟨β, Y, hW, hvalues⟩ := exists_stageWitness_heightOrigin hκ hb hh
    (StagedReg.isStagedHistory_regHist hb hE hR) StagedReg.isRegularDriver_regHist k
  obtain ⟨β₀, hW₀, heq⟩ := exists_stageWitness_of_regHist hb hE hR hW
  refine ⟨β₀, Y, hW₀, ?_⟩
  filter_upwards [hvalues, heq, StagedReg.ae_run_regHist hR] with ω hω hword hrun hlaunch y hy
  rw [hword] at hy ⊢
  have hlaunch' : (ExplState.run κ b jumps spec
      (fun j => StagedReg.regHist spec E j ω) (k + 1)).2.2.2.1 k ≠ none := by
    rw [hrun (k + 1)]
    exact hlaunch
  rcases hω hlaunch' y hy with hOrig | ⟨j, hj, hjlaunch, hheight⟩
  · exact Or.inl hOrig
  · rw [hrun (j + 1)] at hjlaunch
    exact Or.inr ⟨j, hj, hjlaunch, hheight⟩

/-- Schedule-word classification for the original family, using only
`StagedPiecesRegular`. This applies to arbitrary seeds and all schedule
angles; it supplies a numerical alphabet without erasing its original-data
alternative. -/
theorem exists_scheduleWitness_original_or_sideH_reg {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {x₀ : ℝ} {gw2 : Bool} {τ₀ : ℝ≥0}
    {l : List (ℝ × ℝ≥0)} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (x₀, gw2, scheduleProgram τ₀ l) E)
    (hR : StagedPiecesRegular κ b jumps P (x₀, gw2, scheduleProgram τ₀ l) E) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (x₀, gw2, scheduleProgram τ₀ l) E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps (x₀, gw2, scheduleProgram τ₀ l)
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        ∀ y ∉ (β ω).jumps,
          (∃ x ∉ jumps, (β ω).fn y = b x) ∨ Lh.SideH κ l ((β ω).fn y) := by
  obtain ⟨β, Y, hW, hvalues⟩ := exists_stageWitness_heightOrigin_reg hκ hb hh hE hR k
  refine ⟨β, Y, hW, ?_⟩
  filter_upwards [hvalues] with ω hω hlaunch y hy
  exact (hω hlaunch y hy).original_or_sideH

end InteractingSLE.Theorem14.SB.S3
