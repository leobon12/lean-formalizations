/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3RetainedData

/-!
# S3: the conditional word law through every finite instruction

The launch branch uses the actual stopped record. On the no-launch event,
the retained past has the same trace as the preceding past, and the real
chart translation transports its conditional word law.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- Without a launch, the old field retains its old word law under the
new past. The statement uses the entire new conditional kernel. -/
theorem ae_kernelWord_noLaunch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    (h𝒢 : pastSigma κ b jumps spec E (k + 1) ≤ mΩ)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hY : Measurable Y) (hsort : ∀ᵐ ω ∂P, (β ω).IsSorted)
    (hlaw : ∀ᵐ ω ∂P, IsGFFWithBoundaryData
      (condExpKernel P (pastSigma κ b jumps spec E k) ω) Y (β ω).fn (β ω).jumps) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω)
        Y (β ω).fn (β ω).jumps := by
  apply ae_isGFFWithBoundaryData_condExpKernel h𝒢 (hsort.mono fun _ hs _ => hs) hY
  intro φ
  have hCF := ae_condExp_gaussCF_of_kernel
    ((pastSigma_mono spec E (Nat.le_succ k)).trans h𝒢) hY
    (G := univ) (hsort.mono fun _ hs _ => hs) (hlaw.mono fun _ hl _ => hl) φ
  have hCE := ae_condExp_noLaunch_past hb hEm hreg k h𝒢
    (GFF.integrable_exp_I_mul (P := P) ((LQGMetric.measurable_distOn_apply φ).comp hY))
  filter_upwards [hCF, hCE] with ω hcf hce hn
  exact (hce hn).trans (hcf (mem_univ ω))

/-- The actual word/field update has its conditional GFF law at every
sample, provided the instruction has finite allotted time. No next launch
is required, including after terminal stops. -/
theorem ae_kernelWord_nextRetained {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    (htime : ∀ ω, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      min (instrTime spec k) (E k ω).2 ≠ ⊤)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y)
    (hsort : ∀ᵐ ω ∂P, (β ω).IsSorted)
    (hlaw : ∀ᵐ ω ∂P, IsGFFWithBoundaryData
      (condExpKernel P (pastSigma κ b jumps spec E k) ω) Y (β ω).fn (β ω).jumps) :
    ∀ᵐ ω ∂P, IsGFFWithBoundaryData
      (condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω)
      (nextRetainedField κ b jumps spec E k Y)
      (nextRetainedWord κ b jumps spec E k β ω).fn
      (nextRetainedWord κ b jumps spec E k β ω).jumps := by
  classical
  let N : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none}
  have hN : MeasurableSet[pastSigma κ b jumps spec E (k + 1)] N :=
    (pastSigma_mono spec E (Nat.le_succ k)) _
      (measurableSet_noLaunch_pastSigma hb (fun j => hE.1 j) hreg k)
  have hNo := ae_kernelWord_noLaunch hb (fun j => hE.1 j) hreg (hE.2.1 (k + 1)) hW.2.1 hsort hlaw
  have hShift := ae_kernelWord_flowField (hE.2.1 (k + 1)) hW.2.1 hN
    (hsort.mono fun _ hs _ => hs) hNo (measurable_recAmt_pastSigma hb (fun j => hE.1 j) hreg k)
  have hPost := postWord_kernel_of_stageWitness hκ hb hh hE hreg hW
  have hNew := measurable_nextRetainedField hb (fun j => hE.1 j) hreg (hE.2.1 (k + 1)) hW.2.1
  filter_upwards [hShift, hPost,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) (hE.2.1 (k + 1)) hN,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) (hE.2.1 (k + 1)) hN.compl]
    with ω hs hp hn hc
  by_cases hω : ω ∈ N
  · change (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none at hω
    have he : (fun ω' => flowField (WalkInf.recAmt κ b jumps spec E k ω') 0 (Y ω')) =ᵐ[
        condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω]
        nextRetainedField κ b jumps spec E k Y := by
      filter_upwards [hn hω] with ω' hω'
      exact (ite_eq_left hω').symm
    simpa only [nextRetainedWord, ite_eq_left hω] using
      isGFFWithBoundaryData_congr_ae (hs hω) hNew he
  · change (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none at hω
    have he : (fun ω' => recField κ
          (pastMap κ b jumps spec E (k + 1) ω' (Fin.last k)) (Y ω')) =ᵐ[
        condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω]
        nextRetainedField κ b jumps spec E k Y := by
      filter_upwards [hc hω] with ω' hω'
      exact (ite_eq_right hω').symm
    simpa only [nextRetainedWord, ite_eq_right hω] using
      isGFFWithBoundaryData_congr_ae
        (hp hω (htime ω hω)) hNew he

end InteractingSLE.Theorem14.SB.S3
