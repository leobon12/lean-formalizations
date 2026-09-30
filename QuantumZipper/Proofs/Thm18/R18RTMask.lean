import QuantumZipper.Proofs.Thm18.R18RTMaskAsm
import QuantumZipper.Proofs.Thm18.R18RTMaskNeg
import QuantumZipper.Proofs.Thm18.R18RTNodes
import QuantumZipper.Proofs.Thm18.R18T6Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT2 (D82): masked exactness of unzipping the wedge, a.s. wiring

Sheffield, arXiv:1012.4797, §4.1 p. 48 ("`h` may be defined arbitrarily on the measure-zero set
`η`") and Theorem 1.8 (p. 26); Berestycki–Powell, arXiv:2404.16642, Thm 8.16 and Rem 8.10
(p. 283). In the Theorem 1.8 setting, a.s. the masked data of `Z^LEN_{−ℓ}` of the pieces
(`zipLenDownMA`) and of the configuration (`zipLenDownA`) coincide
(`maskExactFull_of_core`), hence `MaskExactAStmt` (`maskExactAStmt_of_core`).

Proved here (deterministic, `R18RTMaskAsm.lean`, plus T6): the driver read from the masked data is
the SLE driver, the carried area is the area read from the masked data (T6), the area scale of the
unzipped wedge is positive (as in T6Main), and the deterministic reduction.

Open inputs (each a single statement, strictly smaller than the target):
* `MaskPullCoreStmt` — the core estimate: a.s. the wedge field and the field read off its curve
  have the same regularized pairings with every folded dyadic circle that stays off the unzipped
  remaining curve, pulled back by `f_s⁻¹`. Mathematically: `readOffField` agrees with `Y` at all
  folded circles off `η`, so the difference is `lim_k ∫_{A_k} (avgReg · k)` over the set `A_k` of
  points `2^{1-k}`-close to `η[0,s]`; log growth of circle averages (Hu–Miller–Peres,
  Ann. Probab. 38 (2010), Prop 2.1) against the Beurling bound `ν(N_ε(η[0,s])) ≤ C ε^β`.
* `UnzCurveNegStmt` — geometric (Rohde–Schramm): a.s. for every `s ≥ 0` the unzipped remaining
  curve `f_s(η[s,∞))` does not meet the negative half-line (it meets `ℝ` only at `0`), so that the
  length of the left open arc `(O⁻_s, 0)` is read off the curve.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **Core estimate of RT2** (open): a.s. the wedge field and the field read off its curve have
the same regularized pairings with all folded dyadic circles off the unzipped remaining curve,
pulled back by the inverse forward maps. -/
def MaskPullCoreStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ᵐ ω ∂P, PullOffAgree (drive (γ ^ 2) B ω) (Y ω)
      (readOffField (offData (wedgeConfig γ B Y ω)))

/-- **Geometric input of RT2** (open, Rohde–Schramm): a.s., for every capacity time `s ≥ 0`, the
remaining SLE curve unzipped by `s` (the curve of `outDrv W s 1`, i.e. of `W(s+·) − W(s)`) does
not meet the negative half-line. -/
def UnzCurveNegStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, t < 0 →
      (t : ℂ) ∉ curveOf (outDrv (drive (γ ^ 2) B ω) s 1)

/-- The driver read from the masked data of the wedge configuration is the SLE driver. -/
theorem drvOfData_offData_wedge (γ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample)
    (ω : Ω) : drvOfData (offData (wedgeAConfig γ B Y ω).toPair) = drive (γ ^ 2) B ω := by
  funext s
  simp only [drvOfData, offData, wedgeAConfig, AreaConfig.toPair, drive]
  congr 2
  apply NNReal.eq
  simp only [Real.coe_toNNReal']
  exact max_eq_left (le_max_right _ _)

/-- A.s. positivity of the area scale of the unzipped wedge (the argument of
`R18.ae_zipLenDownA_area_eq_and_good`). -/
theorem ae_areaScale_zipCapDownA_wedge_pos {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (ℓ : ℝ) :
    ∀ᵐ ω ∂P, 0 < areaScale (zipCapDownA γ (lenTimeOpen γ ℓ (wedgeAConfig γ B Y ω).toPair)
      (wedgeAConfig γ B Y ω)).area := by
  have hP := isPStarSample_of_setting hS
  have hAA := LocLen.pStarAreaAll_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds (γ ^ 2) P Y B hP
  rw [Real.sqrt_sq hS.1.le] at hAA
  filter_upwards [unzipArea_holds γ P B Y hS, D74.ae_wedgeConfig_snd_good hS, hAA]
    with ω hA hω haa
  set c := wedgeAConfig γ B Y ω with hcdef
  have hT : 0 ≤ downTime γ ℓ c := lenTimeOpen_nonneg _ _ _
  have hAT : ∀ S : Set ℂ, MeasurableSet S → S ⊆ H →
      qAreaMeasure γ (unzippedField γ c.toPair (downTime γ ℓ c)) S =
        c.area (fwdMapInv c.drv (downTime γ ℓ c) '' S) :=
    fun S hSm hSH => hA _ hT S hSm hSH
  have hscale := areaScale_zipCapDownA_eq (c := c) hω.1 hω.2 hT hAT
  show 0 < areaScale (zipCapDownA γ (downTime γ ℓ c) c).area
  rw [hscale]
  obtain ⟨h1, h2⟩ := haa _ hT
  exact E6.scaleParam_pos_of_area h1 h2

/-- **RT2, full masked form**, from the core estimate and the geometric input. -/
theorem maskExactFull_of_core (hCore : MaskPullCoreStmt) (hNeg : UnzCurveNegStmt) :
    ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample), Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
      ∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
        offData (zipLenDownMA γ ℓ (wedgeAConfig γ B Y ω)).toPair =
          offData (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair := by
  intro γ Ω _ P _ B Y hS hIn ℓ _
  filter_upwards [hCore γ P B Y hS hIn, hNeg γ P B Y hS hIn, ae_wedgeAConfig_area_eq hS hIn,
    ae_areaScale_zipCapDownA_wedge_pos hS ℓ] with ω hpull hneg harea ha
  unfold zipLenDownMA
  symm
  refine offData_zipLenDownA_eq_of_pullOff ?_ ?_ ?_ hneg ha
  · exact (drvOfData_offData_wedge γ B Y ω).symm
  · exact harea
  · show PullOffAgree (drive (γ ^ 2) B ω) (Y ω) (readOffField (offData (wedgeConfig γ B Y ω)))
    exact hpull

/-- **The geometric input of RT2 holds** (from the Rohde–Schramm facts of `Thm18Inputs` and
`RS.ae_radialGood_drive`; deterministic part `neg_real_not_mem_curveOf_outDrv`). -/
theorem unzCurveNegStmt_holds : UnzCurveNegStmt := by
  intro γ Ω _ P _ B Y hS hIn
  have hκ : 0 < γ ^ 2 := by have := hS.1; positivity
  have hκ4 : γ ^ 2 < 4 := by have := hS.1; have := hS.2.1; nlinarith
  filter_upwards [RS.ae_radialGood_drive hS.2.2.1 hκ (by linarith), hIn.2.2] with ω hRG hω
  intro s hs t ht
  exact neg_real_not_mem_curveOf_outDrv hRG hω.1.2.2.1 hω.1.2.2.2.1 hω.1.2.2.2.2 hs
    (hω.2.1 s hs) ht

/-- **RT2, full masked form**, from the core estimate alone. -/
theorem maskExactFull_of_pullCore (hCore : MaskPullCoreStmt) :
    ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample), Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
      ∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
        offData (zipLenDownMA γ ℓ (wedgeAConfig γ B Y ω)).toPair =
          offData (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair :=
  maskExactFull_of_core hCore unzCurveNegStmt_holds

end R18
end QuantumZipper
