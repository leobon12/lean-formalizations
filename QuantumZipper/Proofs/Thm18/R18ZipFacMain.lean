import QuantumZipper.Proofs.Thm18.R18ZipFacCore
import QuantumZipper.Proofs.Thm18.R18ZipFacScale
import QuantumZipper.Proofs.Thm18.R18T6Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 ZIPFACTOR (D81), part 3: `G4ZipFactorFullAStmt` from X1

Sheffield, arXiv:1012.4797, Theorem 1.8 (1), (3) (p. 26): `Z^LEN_t` is the inverse of
`Z^LEN_{−t}`, a.s. uniquely defined via conformal welding, hence preserves the law. The paper
treats `Z^LEN_t` as a measurable map of the configuration; here that is proved on the data:

* the length-welding driver is read measurably from the circle coordinates on the Borel partial
  graph `GamS` (Lusin–Souslin, Kechris, *Classical Descriptive Set Theory*, Thm 15.1, via
  `exists_lenDrvReading_of_good`, with the Borel good set `exists_goodSet_allTimes` of T4b);
* a.s. the unzipped configuration `Z_{−t} c` has its data in the reading set (the time reversal
  of the SLE driver is a good welding driver, `g4UpWeldCoreAStmt_of_X1`, as in the proof of
  `g4WeldAStmt_holds`), hence so has `c` (E6 on the full data, `map_cfgData_zipLenDownA`);
* a.s. both fields are LQG-good and the carried area is the field's own area (T3, T6), so
  `offData (Z_t x) = maskSel (phiFull γ F (cfgData x))` (`ZipFac.offData_zipLenA_eq`);
* `phiFull` is measurable: Loewner flow in the driver (`measurable_psiZ`,
  `revInvLogDerivMeasStmt_holds`, `measurable_rvS_H`), field coordinates
  (`g4SurrogateZipDataMeasStmt_holds`), scale (`measurable_areaScale_map`).

Own assembly (measurability bookkeeping on top of the cited selection theorem).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G1ZA1c LocLen D3Plus Thm14WeldingData Thm14GoodDriverSet

theorem isLQGGood_fromC_iff {γ : ℝ} (x : FieldSample) :
    IsLQGGood γ (E1.fromC (CoordsFull.coordsFull x)) ↔ IsLQGGood γ x := by
  have h : CoordsFull.coordsFull x = CoordsFull.coordsFull (E1.fromC (CoordsFull.coordsFull x)) :=
    (E1.coordsFull_fromC x).symm
  have hc : Factorization.coords x = Factorization.coords (E1.fromC (CoordsFull.coordsFull x)) :=
    (WedgeCan4.piC_coordsFull x).symm.trans
      ((congrArg WedgeCan4.piC h).trans (WedgeCan4.piC_coordsFull _))
  exact (WedgeGood.isLQGGood_congr_coords hc).symm

theorem measurableSet_goodData (γ : ℝ) :
    MeasurableSet {d : E6.FullData | IsLQGGood γ (E1.fromC d.1.1)} :=
  measurable_fromC_data' (GoodMeas.measurableSet_isLQGGood γ)

/-- A.s. the unzipped configuration has its circle certificates and a good welding driver from
the Borel good set (the argument of `g4WeldAStmt_holds`). -/
theorem ae_zipLenDownA_goodDrv (hX1 : BaseFin.BaseFiniteStmt) {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y)
    (hE6A : E6ALaw γ P B Y) (hEq : LenEqArc γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Good : Set PathT} (hGood : ∀ p ∈ Good, GoodP p)
    (hGae : ∀ᵐ ω ∂P, ∀ t' a : ℝ, 0 < t' → 0 < a → ∃ p ∈ Good, p.2 = t' / a ^ 2 ∧
        ∀ u : Icc (0 : ℝ) 1, p.1 u = gStarVal (drive (γ ^ 2) B ω) t' u) :
    ∀ᵐ ω ∂P, CertC γ (CoordsFull.coordsFull (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld) ∧
      ∃ p ∈ Good, IsLenWeldingDriver γ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld ℓ
        (p.2, sclDrv p) := by
  have hU := g4UpWeldCoreAStmt_of_X1 hX1 γ P B Y hS hIn hE6A hEq ℓ hℓ
  have hE6 := e6StmtArc_of_X1 hX1
  have hum := unzipMeasArc_of_X1 hX1
  set c := wedgeConfig γ B Y with hc
  set c' := fun ω => zipLenDownArc γ ℓ (c ω) with hc'
  have hmc : AEMeasurable (fun ω => Thm18Asm.cfgData (c ω)) P :=
    aemeasurable_cfgData_wedgeConfig hS hIn
  have hmc' : AEMeasurable (fun ω => Thm18Asm.cfgData (c' ω)) P :=
    aemeasurable_cfgData_zipLenDownArc hum hS hℓ
  have hlaw : P.map (fun ω => Thm18Asm.cfgData (c' ω)) =
      P.map (fun ω => Thm18Asm.cfgData (c ω)) := e6Arc_thm18 hE6 hS ℓ hℓ
  have hcert' : ∀ᵐ ω ∂P, Thm18Asm.cfgData (c' ω) ∈ {d : E6.FullData | CertC γ d.1.1} :=
    Cor15Group.ae_mem_of_map_eq ((measurable_fst.comp measurable_fst) (measurableSet_certC γ))
      hmc' hmc hlaw (g4WedgeCertStmt γ P B Y hS hIn)
  filter_upwards [hU, ae_toPair_zipLenDownA_eq hS ℓ, D74.ae_wedgeConfig_snd_good hS, hIn.2.2,
    hcert', hGae] with ω hu htp hω hin hcw hG
  obtain ⟨ha, ht, hz, hwe⟩ := hu
  have hfld : (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld = (c' ω).1 :=
    congrArg Prod.fst htp
  rw [hfld] at hz hwe ⊢
  set t := lenTimeOpen γ ℓ (wedgeAConfig γ B Y ω).toPair with htdef
  set a := areaScale (zipCapDownA γ t (wedgeAConfig γ B Y ω)).area with hadef
  have hpe : upDrvA γ ℓ (wedgeAConfig γ B Y ω) = revDrv (drive (γ ^ 2) B ω) t a := rfl
  rw [hpe] at hz hwe
  have hp0 : 0 < (revDrv (drive (γ ^ 2) B ω) t a).1 := div_pos ht (pow_pos ha 2)
  have hp : IsLenWeldingDriver γ (c' ω).1 ℓ (revDrv (drive (γ ^ 2) B ω) t a) := by
    refine ⟨hp0.le, ?_, ?_, Or.inr ?_, hz, hwe⟩
    · exact ((hω.1.comp (continuous_const.sub (continuous_const.mul continuous_id))).sub
        continuous_const).div_const _
    · simp [revDrv]
    · exact isSimpleCurveHull_revDrv hω.1 hω.2 ht ha hin.1 (hin.2.1 _ ht.le)
  obtain ⟨p, hpG, hpT, hpg⟩ := hG t a ht ha
  have hEqOn := sclDrv_eqOn_revDrv ht ha hpT hpg
  rw [hpT] at hEqOn
  have hL0 : IsLenWeldingDriver γ (c' ω).1 ℓ (t / a ^ 2, sclDrv p) :=
    isLenWeldingDriver_of_eqOn (T := t / a ^ 2) (V := (revDrv (drive (γ ^ 2) B ω) t a).2)
      hp (continuous_sclDrv p) (hGood p hpG).2.1 hEqOn
  rw [← hpT] at hL0
  exact ⟨hcw, p, hpG, hL0⟩

/-- A.s. the carried area of the unzipped configuration is the area of its field. -/
theorem ae_zipLenDownA_area_eq_qArea {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (ℓ : ℝ) :
    ∀ᵐ ω ∂P, (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).area =
      qAreaMeasure γ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld := by
  have hP := isPStarSample_of_setting hS
  have hG := LocLen.pStarGoodOffAll_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds (γ ^ 2) P Y B hP
  have hAA := LocLen.pStarAreaAll_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds (γ ^ 2) P Y B hP
  rw [Real.sqrt_sq hS.1.le] at hG hAA
  filter_upwards [unzipArea_holds γ P B Y hS, D74.ae_wedgeConfig_snd_good hS, hG, hAA]
    with ω hA hω hg haa
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
  exact (zipLenDownA_area_eq_qAreaMeasure hS.1 hω.1 hω.2 hAT hgT.1 hgT.2.2 ha).1

/-- **`G4ZipFactorFullAStmt` from X1** (⇐ Field–Lawler). -/
theorem g4ZipFactorFullAStmt_of_X1 (hX1 : BaseFin.BaseFiniteStmt) : G4ZipFactorFullAStmt := by
  intro γ Ω _ P _ B Y hS hIn hE6A hEq t ht
  obtain ⟨Good, hGm, hGood, hGae⟩ := exists_goodSet_allTimes hS.1 hS.2.1 hS.2.2.1 (P := P)
  obtain ⟨G, F, hR, hmemG⟩ := exists_lenDrvReading_of_good γ t hGm hGood
  have hfR : Measurable (ZipFac.fR F) := by
    have hp : Measurable fun q : E6.FullData × ℂ => (((drvPath F q.1, (F q.1).1) : PathT), q.2) :=
      (((measurable_drvPath hR.2.1 hR.2.2.1).comp measurable_fst).prodMk
        (hR.2.1.comp measurable_fst)).prodMk measurable_snd
    exact measurable_rvS_H.comp hp
  have hsc : Measurable (ZipFac.scF γ F) :=
    measurable_areaScale_map (ZipFac.measurable_muD γ) (ZipFac.muD_isLocFin γ) hfR
  -- laws and data
  have hmc : AEMeasurable (fun ω => cfgData (wedgeAConfig γ B Y ω).toPair) P :=
    aemeasurable_cfgData_wedgeConfig hS hIn
  have hmy := aemeasurable_cfgData_zipLenDownA hX1 hS ht
  have hlaw := map_cfgData_zipLenDownA hX1 hS ht
  -- the unzipped configuration is in the reading set
  have hyG : ∀ᵐ ω ∂P, cfgData (zipLenDownA γ t (wedgeAConfig γ B Y ω)).toPair ∈ G := by
    filter_upwards [ae_zipLenDownA_goodDrv hX1 hS hIn hE6A hEq ht hGood hGae] with ω h
    exact hmemG _ h.1 h.2
  have hcG : ∀ᵐ ω ∂P, cfgData (wedgeAConfig γ B Y ω).toPair ∈ G :=
    Cor15Group.ae_mem_of_map_eq hR.1 hmc hmy hlaw.symm hyG
  -- goodness
  have hcg : ∀ᵐ ω ∂P, IsLQGGood γ (wedgeAConfig γ B Y ω).fld := by
    filter_upwards [hIn.1] with ω h
    exact h.1
  have hcg' : ∀ᵐ ω ∂P, cfgData (wedgeAConfig γ B Y ω).toPair ∈
      {d : E6.FullData | IsLQGGood γ (E1.fromC d.1.1)} := by
    filter_upwards [hcg] with ω h
    exact (isLQGGood_fromC_iff _).2 h
  have hyg : ∀ᵐ ω ∂P, cfgData (zipLenDownA γ t (wedgeAConfig γ B Y ω)).toPair ∈
      {d : E6.FullData | IsLQGGood γ (E1.fromC d.1.1)} :=
    Cor15Group.ae_mem_of_map_eq (measurableSet_goodData γ) hmy hmc hlaw hcg'
  refine ⟨D74.maskSel ∘ ZipFac.phiFull γ F,
    D74.measurable_maskSel.comp (ZipFac.measurable_phiFull hR hsc), ?_, ?_⟩
  · filter_upwards [hcG, hcg, D74.ae_wedgeConfig_snd_good hS] with ω hG hg hω
    exact ZipFac.offData_zipLenA_eq ht hR hω.1 hω.2 hG hg rfl
  · filter_upwards [hyG, hyg, D74.ae_wedgeConfig_snd_good hS, ae_zipLenDownA_area_eq_qArea hS t]
      with ω hG hg hω ha
    have hd := zipLenDownA_drv_good (γ := γ) (ℓ := t) (c := wedgeAConfig γ B Y ω) hω.1
    exact ZipFac.offData_zipLenA_eq ht hR hd.1 hd.2 hG ((isLQGGood_fromC_iff _).1 hg) ha

end R18
end QuantumZipper
