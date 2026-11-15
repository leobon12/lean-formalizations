/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3RetainedWitness

/-!
# S3: finite-prefix words for the original R51 history

The word factors through the original retained past. Both its conditional
kernel and its physical chart are those of the original history.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- Transfer every part of a full retained-word witness back from the
regularized history to the original history and its exact retained past. -/
theorem exists_retainedWordWitness_of_regHist {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) {k : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : RetainedWordWitness κ b jumps P h spec (StagedReg.regHist spec E) k β Y) :
    ∃ β₀ : Ω → BoundaryWord, RetainedWordWitness κ b jumps P h spec E k β₀ Y ∧ β₀ =ᵐ[P] β := by
  obtain ⟨β₀, hStage, heq⟩ := exists_stageWitness_of_regHist hb hE hR
    (hW.isStageWitness (WalkLaw.stagedPiecesRegular_regHist hR))
  have hm : Measurable (pastMap κ b jumps spec (StagedReg.regHist spec E) k) :=
    measurable_pastMap runMeasStatement hb spec
      (fun j _ => StagedReg.measurable_regHist hE.1 j)
      (fun j _ ω => StagedReg.isRegularDriver_regHist j ω) k le_rfl
  have hm₀ : Measurable (pastMap κ b jumps spec E k) := Measurable.of_comap_le (hE.2.1 k)
  have hK := StagedReg.ae_condExpKernel_eq_of_ae_eq hm hm₀ (StagedReg.ae_pastMap_regHist hR k)
  refine ⟨β₀, ⟨hStage.1, hW.measurable_field, ?_, ?_, ?_, ?_⟩, heq⟩
  · filter_upwards [hW.sorted, heq] with ω hs he
    rw [he]
    exact hs
  · filter_upwards [hW.transport, StagedReg.ae_run_regHist hR] with ω ht hr
    rw [hr k] at ht
    exact ht
  · filter_upwards [hW.law, heq, hK] with ω hl he hk
    rw [he, pastSigma_eq_comap, ← hk]
    exact hl
  · filter_upwards [hW.sides, heq, StagedReg.ae_run_regHist hR] with ω hs he hr
    rw [he]
    intro y hy hyH
    have hyH' : LuM.bdVal (ExplState.run κ b jumps spec
        (fun j => StagedReg.regHist spec E j ω) k).2.2.2.2.1 (y : ℂ) ∈ QuantumZipper.H := by
      rw [hr k]
      exact hyH
    obtain ⟨j, hj, hjL, hjH⟩ := hs y hy hyH'
    rw [hr (j + 1)] at hjL
    exact ⟨j, hj, hjL, hjH⟩

/-- Under exactly R51, every prefix with finite allotted instruction times
has a full physical conditional word for the original retained past. -/
theorem exists_retainedWordWitness_reg {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    (k : ℕ) (htime : HasFiniteOrdinaryTimes spec k) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      RetainedWordWitness κ b jumps P h spec E k β Y := by
  obtain ⟨β, Y, hW⟩ := exists_retainedWordWitness hκ hb hh
    (StagedReg.isStagedHistory_regHist hb hE hR) (WalkLaw.stagedPiecesRegular_regHist hR)
    StagedReg.isRegularDriver_regHist k htime
  obtain ⟨β₀, hW₀, -⟩ := exists_retainedWordWitness_of_regHist hb hE hR hW
  exact ⟨β₀, Y, hW₀⟩

end InteractingSLE.Theorem14.SB.S3
