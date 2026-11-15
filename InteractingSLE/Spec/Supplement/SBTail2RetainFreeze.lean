/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Supplement.CondDriverBridge
import InteractingSLE.Spec.Supplement.KernelTower

/-!
# Retained R51 histories remain fixed under larger conditional pasts

The source erasure argument retains the marked first history and an exterior
field projection. This adapter extends the existing everywhere-regular run
reconstruction to the original R51 history. It does not construct an erasure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Retain

open Exist.Staged Exist.StagedLaw

/-- The full marked R51 run is fixed under any conditional law whose sigma
algebra contains its retained past. Exceptional raw drivers need no correction
in the conclusion. -/
theorem ae_ae_run_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (spec : ExplSpec) {Ω : Type u} {𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) {k : ℕ}
    (h𝒢 : 𝒢 ≤ mΩ) (hpast : pastSigma κ b jumps spec E k ≤ 𝒢) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      ExplState.run κ b jumps spec (fun j => E j ω) k =
        ExplState.run κ b jumps spec (fun j => E j ω₀) k := by
  let := upgradeStandardBorel (PastData k)
  have hpm : Measurable[𝒢] (pastMap κ b jumps spec E k) :=
    (comap_measurable (pastMap κ b jumps spec E k)).mono hpast le_rfl
  have hr := StagedReg.ae_run_regHist hR
  have hm := StagedReg.ae_pastMap_regHist hR k
  filter_upwards [hr, hm, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hr,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hm,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq h𝒢 hpm]
    with ω₀ hr₀ hm₀ hrν hmν hfixed
  filter_upwards [hrν, hmν, hfixed] with ω hrω hmω hω
  have he : pastMap κ b jumps spec (StagedReg.regHist spec E) k ω =
      pastMap κ b jumps spec (StagedReg.regHist spec E) k ω₀ :=
    hmω.trans (hω.trans hm₀.symm)
  have hre := run_eq_of_pastMap_eq spec
    (fun j _ ω => StagedReg.isRegularDriver_regHist j ω) he
  exact (hrω k).symm.trans (hre.trans (hr₀ k))

/-- Launch records, including the current chart and angle, are fixed by the
same retained past even though the new driver's record has not been retained. -/
theorem ae_ae_launches_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (spec : ExplSpec) {Ω : Type u} {𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) {k : ℕ}
    (h𝒢 : 𝒢 ≤ mΩ) (hpast : pastSigma κ b jumps spec E k ≤ 𝒢) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 =
        (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 := by
  filter_upwards [ae_ae_run_eq spec hR h𝒢 hpast] with ω₀ hω₀
  exact hω₀.mono fun _ hω => launches_run_succ_of_run_eq spec hω

end InteractingSLE.Theorem14.SB.Retain
