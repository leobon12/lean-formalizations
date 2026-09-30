import QuantumZipper.Proofs.Thm18.R18RTNodes
import QuantumZipper.Proofs.Thm18.R18ZipReg
import QuantumZipper.Proofs.Thm18.R18E6A
import QuantumZipper.Proofs.Thm18.R18Arc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D82 RT5: the zip scale of `Z_ℓ` applied to `Z_{−ℓ} c₀` is positive

Sheffield, arXiv:1012.4797, Theorem 1.8 (1), p. 26. As in the proof of T7b
(`configEqOff_zipLenUpA_zipLenDownA_of`, R18RoundDown.lean): the selected length-welding driver of
the unzipped field is the reversed driver on `[0, T]` (uniqueness of the welding), so the zipped
area is the original area scaled by `a⁻¹`, whose scale is `a⁻¹ > 0`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G4Core

/-- A.s. the zipped area of `Z^LEN_{−ℓ} c₀` along its selected length-welding driver has positive
scale. -/
theorem rt5_ae_zipScale_pos (hX1 : BaseFin.BaseFiniteStmt) {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, 0 < areaScale (zipWeldUpA γ
      (lenWeldDriver γ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld ℓ).1
      (lenWeldDriver γ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld ℓ).2
      (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω))).area := by
  have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
  have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
  have hN := curveAreaNull_holds γ hS.1 hS.2.1 P B Y hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2
  obtain ⟨hw, -⟩ := Wire4.wedgeZeroRegStmt γ P Y hS.1 hS.2.1 hS.2.2.2.1
  filter_upwards [g4UpWeldCoreAStmt_of_X1 hX1 γ P B Y hS hIn hE6 hEq ℓ hℓ, hN, hw,
    hIn.2.2, D74.ae_curveOf_drive_eq hS, ae_remHull_revDrv hS, D74.ae_wedgeConfig_snd_good hS]
    with ω hu hnull hw1 hin hcurve hrem hgood
  obtain ⟨ha, ht, hz, hwe⟩ := hu
  set c := wedgeAConfig γ B Y ω with hcdef
  set t := lenTimeOpen γ ℓ c.toPair with htdef
  set a := areaScale (zipCapDownA γ t c).area with hadef
  have hc : Continuous c.drv := hgood.1
  have hc0 : c.drv 0 = 0 := hgood.2
  have hsub : fwdHull c.drv t ⊆ curveOf c.drv := by
    show fwdHull (drive (γ ^ 2) B ω) t ⊆ curveOf (drive (γ ^ 2) B ω)
    rw [hcurve, hin.2.1 t ht.le]
    exact image_mono fun x hx => le_of_lt hx.1
  have hK : c.area (fwdHull c.drv t ∩ H) = 0 :=
    measure_mono_null (inter_subset_left.trans hsub) hnull
  have hH : c.area Hᶜ = 0 := E6.awt_qAreaMeasure_compl_H γ (Y ω)
  have h1 : areaScale c.area = 1 := hw1.2
  have hq : IsLenWeldingDriver γ (zipLenDownA γ ℓ c).fld ℓ (revDrv c.drv t a) := by
    refine ⟨by simp only [revDrv]; positivity, by simp only [revDrv]; fun_prop,
      by simp [revDrv], Or.inr ?_, hz, hwe⟩
    exact isSimpleCurveHull_revDrv hc hc0 ht ha hin.1 (hin.2.1 _ ht.le)
  set q := revDrv c.drv t a with hqdef
  have hc₃ : zipLenDownA γ ℓ c = canonAConfig γ (zipCapDownA γ t c) := by
    rw [zipLenDownA]
  have hq0 : 0 < q.1 := by simp only [hqdef, revDrv]; positivity
  have hp' := lenWeldDriver_spec ⟨q, hq⟩
  obtain ⟨hT, hEqOn⟩ := isLenWeldingDriver_eq_of_good hq hq0 (hrem _ _ ht ha) hp'
  rw [hT, zipWeldUpA_congr hq0.le hEqOn.symm]
  have hW'' : Continuous fun s => c.drv (t - s) - c.drv t :=
    (hc.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hfull : c.area.restrict (H \ fwdHull c.drv t) = c.area := by
    refine Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (measure_mono_null ?_
      (measure_union_null hH hK)))
    intro z hz
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_and, not_not] at hz
    by_cases hzH : z ∈ H
    · exact Or.inr ⟨hz hzH, hzH⟩
    · exact Or.inl hzH
  have harea : (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).area =
      c.area.map fun z => ((a : ℂ))⁻¹ * z := by
    have key := zipWeldUpA_canonAConfig_area (γ := γ) ht.le hW'' ha (W₃ := q.2) (fun u _ => rfl)
    rw [zipWeldUpA_zipCapDownA_area ht.le hc hc0, hfull] at key
    rw [hc₃]
    exact key
  rw [harea, areaScale_map_inv_mul _ ha, h1, one_div]
  exact inv_pos.2 ha

end R18
end QuantumZipper
