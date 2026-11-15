/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1GoodEight
import InteractingSLE.Spec.ZhanGT4.A1ForcesSnd

/-!
# Zhan's A.1, (Eight): the small exits are good times; the continuous replacement drivers

Packet PROVE-A1-GOODTIME.

* **`eightSnd_isGoodTime`**: (small direction, frame of `capSnd`: small curve at `x`, large curve at `0`) at every
  frozen large time `σ ≤ S₂ᵐ(y₀)`, the small exit `S₁ᵐ(x₀)` is a good time of the small curve's image chain, both
  for its own driver `extPath W₁` (lifetime `ζ₁`) and for the continuous stopped driver `eightDrv` (lifetime `⊤`,
  the driver of the seeded records `eightRec`).
* **The replacement family** `driveFam κ B₂ = √κ B₂` of the large direction (continuous at every sample, as
  `OwnData.cont` needs): **`eightFst_rDrvFst_drive_eq`** — the masked canonical image driver of the original large
  family (lifetime `lifeEnd`) equals that of the replacement family (lifetime `⊤`) up to the clock of the large exit;
  **`eightFst_imgClk_drive_eq`** — the clocks agree; **`eightFst_capFst_drive_eq`** — so do the caps at the exit.
  FAMILY's identification lemmas (`rDrvFst_eq_seedCapacityDriver`, `hW : (d y).W = extPath (Wj · y)`) apply to the
  replacement family, whose good times are `eightFst_isGoodTime_drive`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Good

open QuantumZipper (H fwdHull drive)
open A2X A1Ref A1Common A1EightSeed A1ELaw A1SeedField A1Asm A1Marg A1EightFin A1Core A1Forces

/-- **The continuous replacement of the large Eight family**: `√κ B₂`. -/
def driveFam {Y : Type*} (κ : ℝ) (B : ℝ≥0 → Y → ℝ) : ℝ≥0 → Y → ℝ := fun t y => Real.sqrt κ * B t y

theorem extPath_driveFam {Y : Type*} (κ : ℝ) (B : ℝ≥0 → Y → ℝ) (y : Y) :
    Strip.extPath (driveFam κ B · y) = drive κ B y := rfl

section Eight

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
  {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
  {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

/-- **(Eight, small direction) the small exit is a good time**, for the small curve's own driver (lifetime `ζ₁`) and
for the continuous stopped driver `eightDrv` (lifetime `⊤`), at every frozen large time protected by the large exit
(uncentred frame of `capSnd`: small curve at `x`, large curve at `0`). -/
theorem eightSnd_isGoodTime (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0} (hσ : σ ≤ eightS₂ x W₂ ζ₂ m y₀) :
    IsGoodTime x (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) σ (eightS₁ x W₁ ζ₁ m x₀) ∧
      IsGoodTime x (eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀) ⊤ 0 (Strip.extPath (W₂ · y₀)) σ
        (eightS₁ x W₁ ζ₁ m x₀) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨-, hgood₁, -, hc₂, -, hgood₂, -, hlt₂⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  set S₁ := eightS₁ x W₁ ζ₁ m x₀ with hS₁
  set S₂ := eightS₂ x W₂ ζ₂ m y₀ with hS₂
  obtain ⟨hlt₁, hS₁pos, -, hK₁⟩ := hgood₁ m x₀
  have hδ : 0 < 2 * cofδ (-x) ![] m := mul_pos two_pos (hF.pp m).sep_pos
  have hsep : ∀ a ∈ cofH₁ (-x) ![] m, ∀ b ∈ cofH₂ (-x) ![] m, 2 * cofδ (-x) ![] m ≤ ‖a - b‖ :=
    fun a ha b hb => by rw [norm_sub_rev]; exact (hF.pp m).sep b hb a ha
  -- the frozen large hull at `σ ≤ S₂`, in the frame where the small curve is at `0`
  have hB : physHull (0 - x) (Strip.extPath (W₂ · y₀)) σ ⊆ cofH₂ (-x) ![] m := by
    obtain ⟨T', hT', hcT'⟩ := exists_gt_continuousOn_extPath (h₂.path y₀).2.2.2.1 (hlt₂ m y₀)
    have hsc : Continuous (A1Ref.stopDrv (Strip.extPath (W₂ · y₀)) S₂) :=
      A1Ref.continuous_stopDrv (hc₂ m y₀) S₂.coe_nonneg
    have heq : EqOn (Strip.extPath (W₂ · y₀)) (A1Ref.stopDrv (Strip.extPath (W₂ · y₀)) S₂) (Icc 0 (σ : ℝ)) :=
      fun u hu => (A1Ref.stopDrv_eqOn _ _ ⟨hu.1, hu.2.trans (NNReal.coe_le_coe.2 hσ)⟩).symm
    rw [zero_sub, A1SeedGeom.physHull_congr_of_continuousOn hcT' hsc.continuousOn σ.coe_nonneg
      ((NNReal.coe_le_coe.2 hσ).trans_lt hT') heq, A1Ref.physHull_eq_fwdHull]
    exact ((QuantumZipper.fwdHull_mono (W := frzPath W₂ (-x) S₂ y₀)).1 (NNReal.coe_le_coe.2 hσ)).trans
      (hgood₂ m y₀).2
  have hdc : Continuous (eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀) := continuous_eightDrv (h₁.path x₀).2.2.2.1 hlt₁
  have hAd : physHull 0 (eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀) S₁ ⊆ cofH₁ (-x) ![] m := by
    rw [A1Ref.physHull_zero]; exact hK₁
  obtain ⟨T', hT', hcT'⟩ := exists_gt_continuousOn_extPath (h₁.path x₀).2.2.2.1 hlt₁
  have hA : physHull 0 (Strip.extPath (W₁ · x₀)) S₁ ⊆ cofH₁ (-x) ![] m := by
    rw [A1SeedGeom.physHull_congr_of_continuousOn hcT' hdc.continuousOn S₁.coe_nonneg hT'
      (fun u hu => (A1Ref.stopDrv_eqOn _ _ hu).symm)]
    exact hAd
  refine ⟨A1Marg.isGoodTime_sub.2 (isGoodTime_of_sep hT' hcT' hS₁pos (by rwa [ENNReal.ofReal_coe_nnreal]) hδ hA
    hB hsep), A1Marg.isGoodTime_sub.2 (isGoodTime_of_sep (T' := S₁ + 1) (by linarith) hdc.continuousOn hS₁pos
    ENNReal.ofReal_lt_top hδ hAd hB hsep)⟩

/-- **(Eight, large direction) the clocks of the original and replacement drivers agree at the exit.** -/
theorem eightFst_imgClk_drive_eq (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) (y₀ : Y) (σ : ℝ≥0) (w : ℝ → ℝ) :
    A1Ref.imgClk 0 (drive κ B₂ y₀) x w σ (eightS₂ x W₂ ζ₂ m y₀) =
      A1Ref.imgClk 0 (Strip.extPath (W₂ · y₀)) x w σ (eightS₂ x W₂ ζ₂ m y₀) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  obtain ⟨-, -, -, -, -, -, -, hlt₂⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cof hne)
  obtain ⟨hdc, -, -, -, -, hdrive, -, -⟩ := eightFst_frame hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (s := 0)
    (NNReal.coe_nonneg _)
  obtain ⟨T', hT', hcT'⟩ := exists_gt_continuousOn_extPath (h₂.path y₀).2.2.2.1 (hlt₂ m y₀)
  exact A1SeedGeom.imgClk_congr σ.coe_nonneg (fun _ _ => rfl) (hdc y₀).continuousOn hcT' hT' (hdrive y₀)

/-- **(Eight, large direction) the replacement family has the same masked canonical image driver** as the original
large family, up to the clock of the large exit, at every frozen small time protected by the small exit. -/
theorem eightFst_rDrvFst_drive_eq (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0} (hσ : σ ≤ eightS₁ x W₁ ζ₁ m x₀) {live live' : ℝ≥0 → X → Prop}
    (hlive : live σ x₀) (hlive' : live' σ x₀) {r : ℝ≥0}
    (hr : (r : ℝ) ≤ A1Ref.imgClk 0 (Strip.extPath (W₂ · y₀)) x (Strip.extPath (W₁ · x₀)) σ (eightS₂ x W₂ ζ₂ m y₀)) :
    rDrvFst live' 0 (driveFam κ B₂) (fun _ => ⊤) x W₁ (fun _ => σ) r (x₀, y₀) =
      rDrvFst live 0 W₂ (fun y => lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) x W₁ (fun _ => σ) r (x₀, y₀) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  obtain ⟨-, hgood₁, -⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cof hne)
  obtain ⟨hdc, hd0, -, -, -, hdrive, -, -⟩ := eightFst_frame hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (s := 0)
    (NNReal.coe_nonneg _)
  have hσζ : (σ : ℝ≥0∞) < ζ₁ x₀ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hσ) (hgood₁ m x₀).1
  obtain ⟨τ', hτ', hcτ'⟩ := exists_gt_continuousOn_extPath (h₁.path x₀).2.2.2.1 hσζ
  have hj : ∀ T : ℝ, ENNReal.ofReal T < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) →
      ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 T) := fun T hT =>
    A1Ref.continuousOn_extPath_Icc (h₂.path y₀).2.2.2.1 (hT.trans_le (A2X.P3.lifeEnd_le_lifetime _ _ _))
  have hd0' : driveFam κ B₂ 0 y₀ = 0 := by
    have h := hd0 y₀
    simpa only [drive, Real.toNNReal_zero, driveFam] using h
  refine A1SeedGeom.rDrvFst_congr (z := (x₀, y₀)) (τ := fun _ => σ) hlive hlive' hj (h₂.path y₀).1
    (fun T _ => (show Continuous (Strip.extPath (driveFam κ B₂ · y₀)) from hdc y₀).continuousOn)
    hd0' ⟨τ', hτ', hcτ'⟩ (h₁.path x₀).1 ⟨τ', hτ', hcτ'⟩ (h₁.path x₀).1
    (eightFst_isGoodTime hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y₀ hσ)
    (eightFst_isGoodTime_drive hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y₀ hσ) (fun t ht => ?_) (fun _ _ => rfl) hr
  have h := hdrive y₀ t ⟨t.coe_nonneg, ht⟩
  simpa only [drive, Real.toNNReal_coe, Strip.extPath, driveFam] using h

/-- **(Eight, large direction) the replacement family has the same caps** at the large exit (protected frozen small
time; any liveness predicate holding at `σ`). -/
theorem eightFst_capFst_drive_eq (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0} (hσ : σ ≤ eightS₁ x W₁ ζ₁ m x₀) {live live' : ℝ≥0 → X → Prop}
    (hlive : live σ x₀) (hlive' : live' σ x₀) {T T' : X × Y → ℝ} (hT : T (x₀, y₀) = eightS₂ x W₂ ζ₂ m y₀)
    (hT' : T' (x₀, y₀) = eightS₂ x W₂ ζ₂ m y₀) :
    capFst live' 0 (driveFam κ B₂) (fun _ => ⊤) x W₁ (fun _ => σ) T' (x₀, y₀) =
      capFst live 0 W₂ (fun y => lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) x W₁ (fun _ => σ) T (x₀, y₀) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  obtain ⟨-, hgood₁, -⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cof hne)
  obtain ⟨hdc, hd0, -, -, -, -, -, -⟩ := eightFst_frame hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ (s := 0)
    (NNReal.coe_nonneg _)
  have hσζ : (σ : ℝ≥0∞) < ζ₁ x₀ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hσ) (hgood₁ m x₀).1
  obtain ⟨τ', hτ', hcτ'⟩ := exists_gt_continuousOn_extPath (h₁.path x₀).2.2.2.1 hσζ
  have hj : ∀ T : ℝ, ENNReal.ofReal T < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) →
      ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 T) := fun T hT =>
    A1Ref.continuousOn_extPath_Icc (h₂.path y₀).2.2.2.1 (hT.trans_le (A2X.P3.lifeEnd_le_lifetime _ _ _))
  have hd0' : driveFam κ B₂ 0 y₀ = 0 := by
    have h := hd0 y₀
    simpa only [drive, Real.toNNReal_zero, driveFam] using h
  have hG := eightFst_isGoodTime hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y₀ hσ
  have hG' := eightFst_isGoodTime_drive hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y₀ hσ
  rw [← hT] at hG
  rw [← hT'] at hG'
  rw [capFst_eq_of_isGoodTime (z := (x₀, y₀)) (τ := fun _ => σ) (T := T) hlive hj (h₂.path y₀).1
      ⟨τ', hτ', hcτ'⟩ (h₁.path x₀).1 hG,
    capFst_eq_of_isGoodTime (z := (x₀, y₀)) (τ := fun _ => σ) (T := T') (Wj := driveFam κ B₂)
      hlive' (fun _ _ => (show Continuous (Strip.extPath (driveFam κ B₂ · y₀)) from hdc y₀).continuousOn) hd0'
      ⟨τ', hτ', hcτ'⟩ (h₁.path x₀).1 hG', hT, hT']
  exact congrArg Real.toNNReal
    (eightFst_imgClk_drive_eq hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y₀ σ (Strip.extPath (W₁ · x₀)))

end Eight

end InteractingSLE.ZhanGT4.A1Good
