/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalChart
import InteractingSLE.Spec.Supplement.WalkStageLocalKernel

/-!
# S3: an instruction without a launch retains no new information

On the no-launch event, the next retained record is the fixed initial
record. The larger past therefore restricts to the old past on this
event, and conditional expectations agree there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- The event of no launch is already measured by the old retained past. -/
theorem measurableSet_noLaunch_pastSigma {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    MeasurableSet[pastSigma κ b jumps spec E k]
      {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none} := by
  simpa only [compl_ofPred, not_not] using
    (Lv.measurableSet_launch_pastSigma hb hEm hreg k).compl

/-- An instruction which launches no piece changes the actual chart by
the real translation read from its two forward values at zero. -/
theorem chart_recenter_of_noLaunch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hn : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none) :
    (ExplState.run κ b jumps spec D (k + 1)).2.2.2.2.1 =
      (ExplState.run κ b jumps spec D k).2.2.2.2.1.recenter
        (((ExplState.run κ b jumps spec D k).2.2.2.2.1.1 0 -
          (ExplState.run κ b jumps spec D (k + 1)).2.2.2.2.1.1 0).re) := by
  obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch spec D hn
  simp only [ha, Chart.recenter, sub_sub_cancel, Complex.ofReal_re]

/-- Conditional expectations for the two retained pasts coincide on the
no-launch event, because the new record there is deterministic. -/
theorem ae_condExp_noLaunch_past {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ)
    (h𝒢 : pastSigma κ b jumps spec E (k + 1) ≤ mΩ)
    {X : Ω → ℂ} (hX : Integrable X P) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none →
      P[X | pastSigma κ b jumps spec E (k + 1)] ω = P[X | pastSigma κ b jumps spec E k] ω := by
  let N : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none}
  have hN := measurableSet_noLaunch_pastSigma (κ := κ) (spec := spec) hb hEm hreg k
  apply Restart.ae_condExp_eq_of_trace (pastSigma_mono spec E (Nat.le_succ k)) h𝒢 ?_ hX
  intro B hB
  refine ⟨B ∩ N, ?_, EventuallyEq.rfl⟩
  rw [pastSigma_eq_comap] at hB
  obtain ⟨C, hC, rfl⟩ := hB
  let pad : PastData k → PastData (k + 1) := fun p => WalkLaw.pastSucc p (readRec (fun _ => 0, 0, false))
  have hpad : Measurable pad := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases hi : (i : ℕ) < k
    · simpa only [pad, WalkLaw.pastSucc, hi, ↓reduceDIte] using
        (measurable_pi_apply (X := fun _ : Fin k => RecData) ⟨i, hi⟩)
    · simp only [pad, WalkLaw.pastSucc, hi, ↓reduceDIte]
      exact measurable_const
  have he : pastMap κ b jumps spec E (k + 1) ⁻¹' C ∩ N =
      pastMap κ b jumps spec E k ⁻¹' (pad ⁻¹' C) ∩ N := by
    ext ω
    constructor <;> rintro ⟨hω, hn⟩
    · refine ⟨?_, hn⟩
      have hn' : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none := hn
      change pastMap κ b jumps spec E (k + 1) ω ∈ C at hω
      change pad (pastMap κ b jumps spec E k ω) ∈ C
      rw [WalkLaw.pastMap_succ_eq, ite_eq_left hn'] at hω
      exact hω
    · refine ⟨?_, hn⟩
      have hn' : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none := hn
      change pastMap κ b jumps spec E (k + 1) ω ∈ C
      rw [WalkLaw.pastMap_succ_eq, ite_eq_left hn']
      exact hω
  rw [he]
  refine MeasurableSet.inter ?_ hN
  rw [pastSigma_eq_comap]
  exact ⟨pad ⁻¹' C, hpad hC, rfl⟩

end InteractingSLE.Theorem14.SB.S3
