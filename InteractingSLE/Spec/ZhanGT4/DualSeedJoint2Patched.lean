/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Stopped
import InteractingSLE.Spec.ZhanGT4.A1AsmEight

/-!
# The actual cofinal Eight rectangles have measurable seeded fields

PROVE-ZHAN-GT4-A22. Supplies the measurability clause used by A1-ASSEMBLE's
patched-marginal assembly. The Brownian identity is used only before lifetime.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4.A1Asm
open QuantumZipper (fwdHull)
open A2X A1Marg A1Common A1EightSeed A1SeedField A1Patch
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- Measurability of the actual cofinal rectangles for patched regular Eight
marginals in right-continuous filtrations, without any remaining measurability input. -/
theorem isFieldMeas_eight_of_patched {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    : ∀ m, IsFieldMeas (seedHeightField (eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m))
      (fun _ : Unit => eightS₁ x W₁ ζ₁ m) (fun _ : Unit => eightS₂ x W₂ ζ₂ m) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨hU, hgood₁, hsep₁, hc₂, h0₂, hgood₂, hS₂pos, hlt₂⟩ :=
    eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (eightS₁ x W₁ ζ₁ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₁ (fun ω => (h₁.path ω).2.2.2.1) h₁.evol.2.1 (fun m => (hF.pp m).hull₁)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) m
  have hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₂ (fun ω => (h₂.path ω).2.2.2.1) h₂.evol.2.1 (fun m => (hF.pp m).hull₂)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) (-x) m
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  have hκ : 0 < κ := by linarith
  have hstoch : ∀ m y (t : ℝ), 0 < t → t ≤ eightS₂ x W₂ ζ₂ m y → ∃ B D : ℝ≥0 → X → ℝ,
      IsColumnStoch 𝓖₁ P₁ (kh κ) (fun ω => eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m t (ω, y))
        (eightS₁ x W₁ ζ₁ m) B D := by
    intro m y t _ _
    have hlt : ∀ ω (s : ℝ≥0), s ≤ eightS₁ x W₁ ζ₁ m ω → (s : ℝ≥0∞) < ζ₁ ω := fun ω s hs =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (hgood₁ m ω).1
    exact ⟨B₁, _, isColumnStoch_eightRec_of_reg hk h₁ hB₁ (hs₁ m) (fun ω => (hgood₁ m ω).1)
      (fun ω s hs hsS => (hsep₁ ω s hs (hlt ω s hsS)).1) (fun ω s hs hsS => (hsep₁ ω s hs (hlt ω s hsS)).2)
      (fun ω s hsS => smallEight_sepP_of_good hx (h₁.path ω) (hg₁ ω) s (hlt ω s hsS))⟩
  have hW₂ : ∀ m y (u : ℝ≥0), u ≤ eightS₂ x W₂ ζ₂ m y → W₂ u y = Real.sqrt κ * B₂ u y := by
    intro m y u hu
    have huζ : (u : ℝ≥0∞) < ζ₂ y := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) (hlt₂ m y)
    have hw := (h₂.path y).2.2.2.2.2.2.2.2.2.2.2.2.1 u huζ
    simpa only [Fin.sum_univ_one, Matrix.cons_val_zero, zero_div, intervalIntegral.integral_zero,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero] using hw
  have hB0 : ∀ y, B₂ 0 y = 0 := by
    intro y
    have hw := hW₂ 0 y 0 (show (0 : ℝ≥0) ≤ eightS₂ x W₂ ζ₂ 0 y from bot_le)
    rw [h0₂ y] at hw
    exact (mul_eq_zero.mp hw.symm).resolve_left (Real.sqrt_pos.2 hκ).ne'
  exact isFieldMeas_eight_of_prefixBrownian 𝓖₁ 𝓖₂ (eightS₁ x W₁ ζ₁) (eightS₂ x W₂ ζ₂)
    (cofH₁ (-x) ![]) (cofH₂ (-x) ![]) (cofδ (-x) ![]) (cofq (-x) ![]) (cofd (-x) ![]) (cofTm (-x) ![])
    hs₁ hs₂ hF.pp h₁.path rfl rfl hgood₁ hsep₁ hκ B₂ h₂.evol.1 hB₂ hB0 hW₂
    (fun m y => NNReal.coe_pos.1 (hS₂pos m y)) hgood₂ hstoch

end InteractingSLE.ZhanGT4.A1Asm
