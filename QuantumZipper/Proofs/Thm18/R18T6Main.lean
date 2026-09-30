import QuantumZipper.Proofs.Thm18.R18T6Curve
import QuantumZipper.Proofs.Thm18.R18T6Meas
import QuantumZipper.Proofs.Zipper.LocLenPStarGood
import QuantumZipper.Proofs.Zipper.HitScaleZip
import QuantumZipper.Proofs.RS.TipA
import QuantumZipper.Proofs.RS.TipB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T6 (R18-AREAREAD), part 4: the a.s. identifications

In the Theorem 1.8 setting, almost surely

* `ae_wedgeAConfig_area_eq` (part 2): `(wedgeAConfig γ B Y ω).area = areaOfData γ (masked data)`;
* `ae_zipLenDownA_area_eq`: for every `ℓ`, `(zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).area =
  areaOfData γ (masked data of Z^LEN_{−ℓ})`.

Inputs (all proved): the unzipping area rule T3 (`unzipArea_holds`), goodness and area bounds of
the unzipped fields at all times (`LocLen.pStarGoodOffAll_of_yMergeOffTip`,
`LocLen.pStarAreaAll_of_yMergeOffTip`), zero area of `η` (T1, `curveAreaNull_holds`), and the
Rohde–Schramm facts (trace exists at all times, `RS.ae_radialGood_drive`; simple and in `ℍ`,
`RS.ae_sleTrace_simple_of_le_four`; hull = trace image, `Thm18Inputs`). Sheffield p. 17 ("both
`h` and `η` are determined by the pair") and p. 48 (`η` has measure zero). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **The carried area of `Z^LEN_{−ℓ}` of the wedge is the area read from its masked data**, and
its field has a global area limit (a.s., for every fixed `ℓ`). -/
theorem ae_zipLenDownA_area_eq_and_good {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (ℓ : ℝ) :
    ∀ᵐ ω ∂P, (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).area =
      areaOfData γ (offData (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair) ∧
      IsVagueLimitOn H (areaApprox γ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld)
        (qAreaMeasure γ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld) := by
  have hκ : 0 < γ ^ 2 := by have := hS.1; positivity
  have hκ4 : γ ^ 2 < 4 := by have := hS.1; have := hS.2.1; nlinarith
  have hP := isPStarSample_of_setting hS
  have hG := LocLen.pStarGoodOffAll_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds (γ ^ 2) P Y B hP
  have hAA := LocLen.pStarAreaAll_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds (γ ^ 2) P Y B hP
  rw [Real.sqrt_sq hS.1.le] at hG hAA
  filter_upwards [unzipArea_holds γ P B Y hS, D74.ae_wedgeConfig_snd_good hS, hG, hAA,
    RS.ae_radialGood_drive hS.2.2.1 hκ (by linarith),
    RS.ae_sleTrace_simple_of_le_four hS.2.2.1 hκ hκ4.le, hIn.2.2,
    curveAreaNull_holds γ hS.1 hS.2.1 P B Y hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2]
    with ω hA hω hg haa hRG hsimp hRS hnull
  set c := wedgeAConfig γ B Y ω with hcdef
  have hT : 0 ≤ downTime γ ℓ c := lenTimeOpen_nonneg _ _ _
  have hAT : ∀ S : Set ℂ, MeasurableSet S → S ⊆ H →
      qAreaMeasure γ (unzippedField γ c.toPair (downTime γ ℓ c)) S =
        c.area (fwdMapInv c.drv (downTime γ ℓ c) '' S) :=
    fun S hSm hSH => hA _ hT S hSm hSH
  have hgT := hg _ hT
  have hscale := areaScale_zipCapDownA_eq (c := c) hω.1 hω.2 hT hAT
  have ha : 0 < areaScale (zipCapDownA γ (downTime γ ℓ c) c).area := by
    rw [hscale]
    obtain ⟨h1, h2⟩ := haa _ hT
    exact E6.scaleParam_pos_of_area h1 h2
  refine ⟨zipLenDownA_area_eq_areaOfData hS.1 hω.1 hω.2 hAT hgT.1 hgT.2.2 ha
    (zipLenDownA_curve_null hRG hsimp.1 hsimp.2 hRS.2.1 hnull ha), ?_⟩
  exact (zipLenDownA_area_eq_qAreaMeasure hS.1 hω.1 hω.2 hAT hgT.1 hgT.2.2 ha).2

/-- **The carried area of `Z^LEN_{−ℓ}` of the wedge is the area read from its masked data**
(a.s., for every fixed `ℓ`). -/
theorem ae_zipLenDownA_area_eq {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (ℓ : ℝ) :
    ∀ᵐ ω ∂P, (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).area =
      areaOfData γ (offData (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair) :=
  (ae_zipLenDownA_area_eq_and_good hS hIn ℓ).mono fun _ h => h.1

end R18
end QuantumZipper
