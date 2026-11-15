/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2RetainFreeze
import InteractingSLE.Spec.Supplement.GW2aContStepLaunch

/-!
# A zero-capacity launch reveals no additional retained information under R51

The existing zero-record kernel theorem applies to regularized histories.
Almost-sure agreement of retained records transfers its exact kernel equality
to the original family. Neither a positive lifetime nor a new field law is
assumed; the threshold flag is retained throughout.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Retain

open Exist.Staged Exist.StagedLaw GW2aCont

/-- The raw and regularized retained pasts have the same conditional measures
almost surely, even when their sigma-algebras differ on null sets. -/
theorem ae_condExpKernel_regHist {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {spec : ExplSpec}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    ∀ᵐ ω ∂P, condExpKernel P (pastSigma κ b jumps spec (StagedReg.regHist spec E) k) ω =
      condExpKernel P (pastSigma κ b jumps spec E k) ω := by
  have hE' := StagedReg.isStagedHistory_regHist hb hE hR
  rw [pastSigma_eq_comap, pastSigma_eq_comap]
  exact StagedReg.ae_condExpKernel_eq_of_ae_eq
    (measurable_pastMap_of_le hE'.2.1 k) (measurable_pastMap_of_le hE.2.1 k)
    (StagedReg.ae_pastMap_regHist hR k)

/-- The existing constant-record theorem specialized to an actual launch.
This intermediate version uses drivers regular at every realization. -/
theorem ae_zero_stop_kernel_eq_regular {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {spec : ExplSpec} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
        min (instrTime spec k) (E k ω).2 = 0 →
          condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω =
            condExpKernel P (pastSigma κ b jumps spec E k) ω₀ := by
  filter_upwards [hE.2.2.2 k, ae_ae_condExpKernel_succ_eq hE.2.1 k,
    CondDriverBridge.ae_ae_run_eq_of_le spec (fun j _ ω => hreg j ω) (hE.2.1 k) le_rfl]
    with ω₀ hlaunch hK hrun c θ hcθ
  obtain ⟨b', J', hl, _, _, hfl⟩ := hlaunch c θ hcθ
  have hg : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
      lastRec κ b jumps spec E k ω = recOf (instrTime spec k) (E k ω) := by
    filter_upwards [hrun] with ω hω
    apply lastRec_of_launch spec E k
    rw [launches_run_succ_of_run_eq spec hω, hcθ]
    exact Option.some_ne_none _
  exact ae_condExpKernel_succ_eq_of_stop_zero hE.2.1 hreg hK hg
    (ae_lifetime_eq_zero_or_ne hfl)

/-- At a launched zero stop, the original R51 history retains no additional
information. The entire conditional measure is unchanged, including the
field, other histories, exterior projections, and stopping flags. -/
theorem ae_zero_stop_kernel_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {spec : ExplSpec}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
        min (instrTime spec k) (E k ω).2 = 0 →
          condExpKernel P (pastSigma κ b jumps spec E (k + 1)) ω =
            condExpKernel P (pastSigma κ b jumps spec E k) ω₀ := by
  let E' := StagedReg.regHist spec E
  have hE' := StagedReg.isStagedHistory_regHist hb hE hR
  have hK := ae_condExpKernel_regHist hb hE hR k
  have hKnext := ae_condExpKernel_regHist hb hE hR (k + 1)
  have hzero := ae_zero_stop_kernel_eq_regular hE' StagedReg.isRegularDriver_regHist k
  filter_upwards [hzero, hK, StagedReg.ae_run_regHist hR,
    KernelTower.ae_ae_condExpKernel_of_ae (hE.2.1 k) hKnext]
    with ω₀ hz hK₀ hrun hKν c θ hcθ
  have hcθ' : (ExplState.run κ b jumps spec (fun j => E' j ω₀) (k + 1)).2.2.2.1 k =
      some (c, θ) := by
    rw [hrun (k + 1)]
    exact hcθ
  have hz' := hz c θ hcθ'
  rw [hK₀] at hz'
  filter_upwards [hz', hKν] with ω hω hKω hstop
  exact hKω.symm.trans (hω (by simpa only [StagedReg.regHist_snd] using hstop))

end InteractingSLE.Theorem14.SB.Retain
