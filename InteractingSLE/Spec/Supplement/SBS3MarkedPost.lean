/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedWitness

/-!
# S3: the stopped word also exists at finite terminal stops

The post-stage Gaussian law requires the stop to be finite, and does not
require the next instruction to launch. Keep the actual word, genealogy,
measurability and full retained-past conditional law together.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- Measurability of the last retained record, for its exact past sigma algebra. -/
theorem measurable_lastRetainedRecord {Ω : Type u} {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    Measurable[pastSigma κ b jumps spec E (k + 1)]
      (fun ω => pastMap κ b jumps spec E (k + 1) ω (Fin.last k)) := by
  let : MeasurableSpace Ω := pastSigma κ b jumps spec E (k + 1)
  have hpm : Measurable[pastSigma κ b jumps spec E (k + 1)]
      (pastMap κ b jumps spec E (k + 1)) := by
    rw [pastSigma_eq_comap]
    exact comap_measurable _
  exact measurable_pi_iff.1 hpm (Fin.last k)

/-- The existing post-stage characteristic law gives the conditional GFF
law under the entire retained past after a finite stop. -/
theorem postWord_kernel_of_stageWitness {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    {β₀ : Ω → BoundaryWord} {Y₀ : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β₀ Y₀) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      min (instrTime spec k) (E k ω).2 ≠ ⊤ →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω)
        (fun ω' => recField κ (pastMap κ b jumps spec E (k + 1) ω' (Fin.last k)) (Y₀ ω'))
        (stopWord κ (β₀ ω, instrAngle spec k,
          pastMap κ b jumps spec E (k + 1) ω (Fin.last k))).fn
        (stopWord κ (β₀ ω, instrAngle spec k,
          pastMap κ b jumps spec E (k + 1) ω (Fin.last k))).jumps := by
  have hpost := post_stage (spec := spec) (E := E) (ℓ := k) (β := β₀) (Y := Y₀)
    (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
    (fun j _ => hE.1 j) (fun j _ => hreg j) (hE.2.2.2 k)
    hW.1 hW.2.1 hW.2.2.1 hW.2.2.2
  have hR := measurable_lastRetainedRecord (κ := κ) (b := b) (jumps := jumps) spec E k
  have hY : Measurable (fun ω => recField κ
      (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)) (Y₀ ω)) :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => recField κ p.1 p.2)
      (f := fun ω => (pastMap κ b jumps spec E (k + 1) ω (Fin.last k), Y₀ ω))
      (measurable_recField κ) ((hR.mono (hE.2.1 (k + 1)) le_rfl).prodMk hW.2.1)
  have hk := ae_isGFFWithBoundaryData_condExpKernel (hE.2.1 (k + 1))
    (β := fun ω => stopWord κ (β₀ ω, instrAngle spec k,
      pastMap κ b jumps spec E (k + 1) ω (Fin.last k)))
    (M := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none ∧
      min (instrTime spec k) (E k ω).2 ≠ ⊤})
    (Eventually.of_forall fun ω _ => isSorted_stopWord κ _) hY
    (fun φ => (hpost.2 φ).mono fun ω hω hωG => hω hωG.1 hωG.2)
  exact hk.mono fun ω hω hL hfin => hω ⟨hL, hfin⟩

/-- The conditional field after a finite stopped instruction, including a
terminal stop. No launch of instruction `k + 1` is assumed. -/
theorem exists_postWord_heightOrigin {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      Measurable[pastSigma κ b jumps spec E (k + 1)] β ∧ Measurable Y ∧
      (∀ ω, (β ω).IsSorted) ∧
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        ∀ y ∉ (β ω).jumps,
          StageHeight κ b jumps spec (fun j => E j ω) (k + 1) ((β ω).fn y)) ∧
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        min (instrTime spec k) (E k ω).2 ≠ ⊤ →
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω)
          Y (β ω).fn (β ω).jumps) ∧
      ∃ (β₀ : Ω → BoundaryWord) (Y₀ : Ω → DistOn upperHalfPlaneOpens),
        IsStageWitness κ b jumps P h spec E k β₀ Y₀ ∧
        Y =ᵐ[P] (fun ω => recField κ
          (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)) (Y₀ ω)) := by
  obtain ⟨β₀, Y₀, hW, hOrigin⟩ := exists_stageWitness_sorted_heightOrigin hκ hb hh hE hreg k
  let R : Ω → RecData := fun ω => pastMap κ b jumps spec E (k + 1) ω (Fin.last k)
  let β : Ω → BoundaryWord := fun ω => stopWord κ (β₀ ω, instrAngle spec k, R ω)
  let Y : Ω → DistOn upperHalfPlaneOpens := fun ω => recField κ (R ω) (Y₀ ω)
  have hR : Measurable[pastSigma κ b jumps spec E (k + 1)] R :=
    measurable_lastRetainedRecord spec E k
  have hβ : Measurable[pastSigma κ b jumps spec E (k + 1)] β :=
    (measurable_stopWord κ).comp
      ((hW.1.mono (pastSigma_mono spec E (Nat.le_succ k)) le_rfl).prodMk
        (measurable_const.prodMk hR))
  have hY : Measurable Y :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => recField κ p.1 p.2)
      (f := fun ω => (R ω, Y₀ ω)) (measurable_recField κ)
      ((hR.mono (hE.2.1 (k + 1)) le_rfl).prodMk hW.2.1)
  refine ⟨β, Y, hβ, hY, fun _ => isSorted_stopWord κ _, ?_,
    postWord_kernel_of_stageWitness hκ hb hh hE hreg hW, β₀, Y₀, hW, ?_⟩
  · filter_upwards [hOrigin] with ω hω hlaunch
    refine stopWord_values_of_predicate hκ
      (fun y hy => ((hω hlaunch).2 y hy).mono (Nat.le_succ k))
      (instrAngle spec k) (R ω) ?_ ?_
    · exact Or.inr ⟨k, Nat.lt_succ_self k, hlaunch, Or.inr rfl⟩
    · exact Or.inr ⟨k, Nat.lt_succ_self k, hlaunch, Or.inl rfl⟩
  · exact Eventually.of_forall fun _ => rfl

end InteractingSLE.Theorem14.SB.S3
