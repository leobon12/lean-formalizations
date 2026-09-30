import QuantumZipper.Proofs.Thm18.R18T6Defs
import QuantumZipper.Proofs.Thm18.R18AreaNullMain
import QuantumZipper.Proofs.Thm18.R18MuBasic
import QuantumZipper.Proofs.Zipper.LocLenPStarArea

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T6 (R18-AREAREAD), part 2: the carried area is the area read from the masked data

* `ae_wedgeAConfig_area_eq`: a.s. `(wedgeAConfig γ B Y ω).area = areaOfData γ (masked data)`
  (the wedge area is a global vague limit on `ℍ`, `R18T6Defs.areaOfData_offData_eq`, and the curve
  carries no area, T1 `curveAreaNull_holds`; Sheffield p. 48).
* `zipCapDownA_area_eq_qAreaMeasure`, `zipLenDownA_area_eq_qAreaMeasure`: deterministic: when the
  unzipping area rule (T3) holds at the unzipping time and the unzipped field is good, the carried
  area of `Z^LEN_{−ℓ} c` is the quantum area of its own field (DS11 Prop 2.1 for the rescaling);
  `zipLenDownA_area_eq_areaOfData`: hence the area read from its masked data, once its curve
  carries no area.

Own elementary bookkeeping on top of T1, T3 and the rescaling rule.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

theorem isVagueLimitOn_of_hasAreaLimit_R18 {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x)
    {μ : Measure ℂ} (hμ : HasAreaLimit γ x μ) : IsVagueLimitOn H (areaApprox γ x) μ := by
  obtain ⟨F, hF⟩ := hx
  refine ⟨hμ.1, hμ.2.1, fun f hf hfc hfU => ?_⟩
  have := (hμ.2.2 f hf hfc hfU).comp GoodSample.tendsto_one_goodFilter
  refine this.congr fun k => ?_
  simp only [Function.comp, goodRad, GoodSample.areaR_radius γ hF]

theorem isVagueLimitOn_qAreaMeasure_of_good {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    IsVagueLimitOn H (areaApprox γ x) (qAreaMeasure γ x) :=
  isVagueLimitOn_of_hasAreaLimit_R18 hx.1 hx.qAreaMeasure_spec

/-- **The wedge area is the area read from the masked data** (a.s.). -/
theorem ae_wedgeAConfig_area_eq {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    ∀ᵐ ω ∂P, (wedgeAConfig γ B Y ω).area =
      areaOfData γ (offData (wedgeAConfig γ B Y ω).toPair) := by
  filter_upwards [hIn.1, D74.ae_wedgeConfig_snd_good hS,
    curveAreaNull_holds γ hS.1 hS.2.1 P B Y hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2] with ω hG hω hnull
  exact (areaOfData_offData_eq hω.1 hω.2 (isVagueLimitOn_qAreaMeasure_of_good hG.1) hnull).symm

theorem qAreaMeasure_compl_H (γ : ℝ) (x : FieldSample) : qAreaMeasure γ x Hᶜ = 0 := by
  classical
  unfold qAreaMeasure
  split_ifs with h
  · exact h.choose_spec.1
  · rfl

/-- The transported area at time `t` is the unzipped field's area, given the unzipping rule. -/
theorem zipCapDownA_area_eq_qAreaMeasure {γ t : ℝ} {c : AreaConfig} (hc : Continuous c.drv)
    (hc0 : c.drv 0 = 0) (ht : 0 ≤ t)
    (hA : ∀ S : Set ℂ, MeasurableSet S → S ⊆ H →
      qAreaMeasure γ (unzippedField γ c.toPair t) S = c.area (fwdMapInv c.drv t '' S)) :
    (zipCapDownA γ t c).area = qAreaMeasure γ (unzippedField γ c.toPair t) := by
  have hHm : MeasurableSet H := isOpen_H.measurableSet
  have hcompl : (zipCapDownA γ t c).area Hᶜ = 0 := by
    rw [zipCapDownA_area_eq_areaTransport]
    unfold E6.areaTransport
    rw [Measure.map_apply_of_aemeasurable (E6.aemeasurable_fwdMap_restrict hc ht _) hHm.compl,
      Measure.restrict_apply' (E6.measurableSet_compl_fwdHull hc ht)]
    have : fwdMap c.drv t ⁻¹' Hᶜ ∩ (H \ fwdHull c.drv t) = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
        not_and]
      intro hz hzK
      exact hz (FwdHolo.mapsTo_fwdMap hc ht hzK)
    rw [this, measure_empty]
  ext S hS
  have h1 : (zipCapDownA γ t c).area (S \ H) = 0 := measure_mono_null (fun z hz => hz.2) hcompl
  have h2 : qAreaMeasure γ (unzippedField γ c.toPair t) (S \ H) = 0 :=
    measure_mono_null (fun z hz => hz.2) (qAreaMeasure_compl_H γ _)
  rw [← measure_inter_add_diff S hHm, ← measure_inter_add_diff (μ := qAreaMeasure γ _) S hHm,
    h1, h2, add_zero, add_zero,
    hA _ (hS.inter hHm) inter_subset_right, zipCapDownA_area_eq_areaTransport,
    E6.areaTransport_apply hc hc0 ht _ (hS.inter hHm) inter_subset_right]

/-- The unzipping time of `Z^LEN_{−ℓ}`. -/
abbrev downTime (γ ℓ : ℝ) (c : AreaConfig) : ℝ := lenTimeOpen γ ℓ c.toPair

theorem zipLenDownA_fld (γ ℓ : ℝ) (c : AreaConfig) :
    (zipLenDownA γ ℓ c).fld = rescale (unzippedField γ c.toPair (downTime γ ℓ c)) (Qc γ)
      (areaScale (zipCapDownA γ (downTime γ ℓ c) c).area) := rfl

theorem zipLenDownA_area (γ ℓ : ℝ) (c : AreaConfig) :
    (zipLenDownA γ ℓ c).area = (zipCapDownA γ (downTime γ ℓ c) c).area.map
      (fun z => ((areaScale (zipCapDownA γ (downTime γ ℓ c) c).area : ℂ))⁻¹ * z) := rfl

theorem zipLenDownA_drv_good {γ ℓ : ℝ} {c : AreaConfig} (hc : Continuous c.drv) :
    Continuous (zipLenDownA γ ℓ c).drv ∧ (zipLenDownA γ ℓ c).drv 0 = 0 := by
  simp only [zipLenDownA, canonAConfig, zipCapDownA, zipCapDown, AreaConfig.toPair]
  refine ⟨by fun_prop, by simp⟩

/-- **Deterministic**: the carried area of `Z^LEN_{−ℓ} c` is the area of its own field, and that
field has a global area limit, when the unzipping rule holds and the unzipped field is good. -/
theorem zipLenDownA_area_eq_qAreaMeasure {γ ℓ : ℝ} (hγ : 0 < γ) {c : AreaConfig}
    (hc : Continuous c.drv) (hc0 : c.drv 0 = 0)
    (hA : ∀ S : Set ℂ, MeasurableSet S → S ⊆ H →
      qAreaMeasure γ (unzippedField γ c.toPair (downTime γ ℓ c)) S =
        c.area (fwdMapInv c.drv (downTime γ ℓ c) '' S))
    (hr : IsRegularSample (unzippedField γ c.toPair (downTime γ ℓ c)))
    (hμ : ∃ μ, HasAreaLimit γ (unzippedField γ c.toPair (downTime γ ℓ c)) μ)
    (ha : 0 < areaScale (zipCapDownA γ (downTime γ ℓ c) c).area) :
    (zipLenDownA γ ℓ c).area = qAreaMeasure γ (zipLenDownA γ ℓ c).fld ∧
      IsVagueLimitOn H (areaApprox γ (zipLenDownA γ ℓ c).fld)
        (qAreaMeasure γ (zipLenDownA γ ℓ c).fld) := by
  set y := unzippedField γ c.toPair (downTime γ ℓ c) with hy
  set a := areaScale (zipCapDownA γ (downTime γ ℓ c) c).area with hadef
  have hT : 0 ≤ downTime γ ℓ c := lenTimeOpen_nonneg _ _ _
  have hresc := LocLen.qAreaMeasure_rescale_of_area hr hμ hγ ha
  refine ⟨?_, ?_⟩
  · rw [zipLenDownA_area, zipLenDownA_fld, ← hadef, ← hy, hresc,
      zipCapDownA_area_eq_qAreaMeasure hc hc0 hT hA]
    congr 1
    funext z
    rw [div_eq_inv_mul]
  · rw [zipLenDownA_fld, ← hadef, ← hy]
    have hr' := hr.rescale' (Qc γ) ha
    refine isVagueLimitOn_of_hasAreaLimit_R18 hr' ?_
    rw [hresc]
    exact GoodTransforms.hasAreaLimit_rescale hr hγ (LocLen.qAreaMeasure_spec_of_area hr hμ) ha

/-- **Deterministic**: under the same hypotheses, once the curve of `Z^LEN_{−ℓ} c` carries no
carried area, the carried area is the area read from the masked data. -/
theorem zipLenDownA_area_eq_areaOfData {γ ℓ : ℝ} (hγ : 0 < γ) {c : AreaConfig}
    (hc : Continuous c.drv) (hc0 : c.drv 0 = 0)
    (hA : ∀ S : Set ℂ, MeasurableSet S → S ⊆ H →
      qAreaMeasure γ (unzippedField γ c.toPair (downTime γ ℓ c)) S =
        c.area (fwdMapInv c.drv (downTime γ ℓ c) '' S))
    (hr : IsRegularSample (unzippedField γ c.toPair (downTime γ ℓ c)))
    (hμ : ∃ μ, HasAreaLimit γ (unzippedField γ c.toPair (downTime γ ℓ c)) μ)
    (ha : 0 < areaScale (zipCapDownA γ (downTime γ ℓ c) c).area)
    (hnull : (zipLenDownA γ ℓ c).area (curveOf (zipLenDownA γ ℓ c).drv) = 0) :
    (zipLenDownA γ ℓ c).area = areaOfData γ (offData (zipLenDownA γ ℓ c).toPair) := by
  obtain ⟨he, hv⟩ := zipLenDownA_area_eq_qAreaMeasure hγ hc hc0 hA hr hμ ha
  have hd := zipLenDownA_drv_good (γ := γ) (ℓ := ℓ) hc
  rw [he] at hnull ⊢
  exact (areaOfData_offData_eq (x := (zipLenDownA γ ℓ c).toPair) hd.1 hd.2 hv hnull).symm

end R18
end QuantumZipper
