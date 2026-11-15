/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalStep
import InteractingSLE.Spec.Supplement.SBS3MarkedPost

/-!
# S3: one terminal word with its law and physical side labels

Choose a stage witness carrying the physical invariant before taking its
stopped word. The same stopped word then has the full retained-past GFF law
and physical side provenance, including at a terminal nonlaunch.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- A finite post-stop word with its physical side labels and conditional
GFF law, for an everywhere regular family satisfying R51. -/
theorem exists_postWord_interiorStageSides {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      Measurable[pastSigma κ b jumps spec E (k + 1)] β ∧ Measurable Y ∧
      (∀ ω, (β ω).IsSorted) ∧
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        min (instrTime spec k) (E k ω).2 ≠ ⊤ →
        HasInteriorStageSides κ b jumps spec (fun j => E j ω) (k + 1) (β ω) ∧
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω)
          Y (β ω).fn (β ω).jumps) ∧
      ∃ (β₀ : Ω → BoundaryWord) (Y₀ : Ω → DistOn upperHalfPlaneOpens),
        IsStageWitness κ b jumps P h spec E k β₀ Y₀ ∧
        Y =ᵐ[P] (fun ω => recField κ
          (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)) (Y₀ ω)) := by
  obtain ⟨β₀, Y₀, hW, hSides⟩ := exists_stageWitness_interiorStageSides hκ hb hh hE hR hreg k
  let R : Ω → RecData := fun ω => pastMap κ b jumps spec E (k + 1) ω (Fin.last k)
  let β : Ω → BoundaryWord := fun ω => stopWord κ (β₀ ω, instrAngle spec k, R ω)
  let Y : Ω → DistOn upperHalfPlaneOpens := fun ω => recField κ (R ω) (Y₀ ω)
  have hRec : Measurable[pastSigma κ b jumps spec E (k + 1)] R :=
    measurable_lastRetainedRecord spec E k
  have hβ : Measurable[pastSigma κ b jumps spec E (k + 1)] β :=
    (measurable_stopWord κ).comp
      ((hW.1.mono (pastSigma_mono spec E (Nat.le_succ k)) le_rfl).prodMk
        (measurable_const.prodMk hRec))
  have hY : Measurable Y :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => recField κ p.1 p.2)
      (f := fun ω => (R ω, Y₀ ω)) (measurable_recField κ)
      ((hRec.mono (hE.2.1 (k + 1)) le_rfl).prodMk hW.2.1)
  have hpost := post_stage (spec := spec) (E := E) (ℓ := k) (β := β₀) (Y := Y₀)
    (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
    (fun j _ => hE.1 j) (fun j _ => hreg j) (hE.2.2.2 k)
    hW.1 hW.2.1 hW.2.2.1 hW.2.2.2
  refine ⟨β, Y, hβ, hY, fun _ => isSorted_stopWord κ _, ?_,
    β₀, Y₀, hW, Eventually.of_forall fun _ => rfl⟩
  filter_upwards [hSides, hpost.1, postWord_kernel_of_stageWitness hκ hb hh hE hreg hW,
    GW1W.regLaunches_of_stagedPiecesRegular hR] with ω hs hg hl hr hlaunch hfin
  refine ⟨?_, hl hlaunch hfin⟩
  change HasInteriorStageSides κ b jumps spec (fun j => E j ω) (k + 1)
    (stopWord κ (β₀ ω, instrAngle spec k, pastMap κ b jumps spec E (k + 1) ω (Fin.last k)))
  rw [pastMap_last_of_launch hlaunch]
  exact interior_stageSide_post_launch hκ hr hlaunch hfin (hreg k ω)
    (hg hlaunch hfin) (hs hlaunch).2

end InteractingSLE.Theorem14.SB.S3
