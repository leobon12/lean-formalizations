import QuantumZipper.Proofs.Thm18.R18ZipFacDefs
import QuantumZipper.Proofs.Thm18.R18T4bWeld
import QuantumZipper.Proofs.Thm18.G4ZipUp3LogDeriv
import QuantumZipper.Proofs.Thm18.G4ZipUp3SurMeas
import QuantumZipper.Proofs.Thm18.G4ReadZip
import QuantumZipper.Proofs.LQG.GoodMeasurable
import QuantumZipper.Proofs.LQG.WedgeCanonical4
import QuantumZipper.Proofs.LQG.WedgeGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 ZIPFACTOR (D81), part 2: the zip-up along a read driver as a function of the data

Sheffield, arXiv:1012.4797, Theorem 1.8 (1) (p. 26): `Z^LEN_t` is "a.s. uniquely defined (via
conformal welding)". Given a measurable reading `(G, F)` of good length-`t` welding drivers
(`LenDrvReading`, built by Lusin–Souslin, Kechris *Classical Descriptive Set Theory* Thm 15.1,
in `exists_lenDrvReading_of_good`), the masked data of `Z^LEN_t x` is `maskSel (phiFull γ F d)` for
the full data `d = cfgData x` (`offData_zipLenA_eq`), whenever `d ∈ G`, the driver of `x` is
continuous and vanishes at `0`, the field is LQG-good and the carried area is the field's area.
`phiFull` is explicit: the zipped field is read through the circle coordinates and the measurable
surrogate `psiZ F` of the inverse reverse map; the driver through `zipDrvOut`; the scale (1.8)
through the area `muD γ d` of the reconstructed field pushed by the measurable surrogate `fR F`
of the reverse map (`scF`). `measurable_phiFull`: `phiFull` is measurable once `scF` is.

Own elementary argument (bookkeeping on top of the cited uniqueness of welding,
`isLenWeldingDriver_unique_of_good`, and the Loewner/field measurability library).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18
namespace ZipFac

open Thm18Asm

open Classical in
/-- The quantum area of the field reconstructed from the circle coordinates (junk `0` if that
field is not LQG-good). -/
def muD (γ : ℝ) (d : E6.FullData) : Measure ℂ :=
  if IsLQGGood γ (E1.fromC d.1.1) then qAreaMeasure γ (E1.fromC d.1.1) else 0

/-- The measurable surrogate of the reverse map of the read driver, on `ℍ`. -/
def fR (F : E6.FullData → ℝ × (ℝ → ℝ)) (q : E6.FullData × ℂ) : ℂ :=
  if 0 < q.2.im then rvS (drvPath F q.1, (F q.1).1) q.2 else 0

/-- The scale (1.8) of the zip-up, read from the data. -/
def scF (γ : ℝ) (F : E6.FullData → ℝ × (ℝ → ℝ)) (d : E6.FullData) : ℝ :=
  areaScale (((muD γ d).restrict H).map fun z => fR F (d, z))

/-- The full data of the zip-up, read from the data. -/
def phiFull (γ : ℝ) (F : E6.FullData → ℝ × (ℝ → ℝ)) (d : E6.FullData) : E6.FullData :=
  ((CoordsFull.coordsFull (canonicalData γ d (psiZ F d) (scF γ F d)),
      fun ρ : TestFun H => pairRaw (canonicalData γ d (psiZ F d) (scF γ F d)) ρ.1),
    fun s => zipDrvOut (F d).1 (scF γ F d) (F d).2 d.2 s)

theorem measurable_muD (γ : ℝ) : Measurable (muD γ) := by
  classical
  have h := (GoodMeas.measurable_qAreaMeasure_global γ).comp measurable_fromC_data'
  exact h

theorem muD_isLocFin (γ : ℝ) (d : E6.FullData) (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ H) :
    muD γ d K < ∞ := by
  classical
  unfold muD
  split_ifs with h
  · obtain ⟨μ, hμ⟩ := h.2.2
    have hq := LocLen.qAreaMeasure_spec_of_area h.1 ⟨μ, hμ⟩
    exact hq.2.1 K hK hKH
  · simp

/-- On a good field, `muD` of its data is its area. -/
theorem muD_cfgData {γ : ℝ} {x : FieldSample × (ℝ → ℝ)} (hg : IsLQGGood γ x.1) :
    muD γ (cfgData x) = qAreaMeasure γ x.1 := by
  classical
  have h : CoordsFull.coordsFull x.1 = CoordsFull.coordsFull (E1.fromC (CoordsFull.coordsFull x.1)) :=
    (E1.coordsFull_fromC x.1).symm
  have hc : Factorization.coords x.1 = Factorization.coords (E1.fromC (CoordsFull.coordsFull x.1)) :=
    (WedgeCan4.piC_coordsFull x.1).symm.trans
      ((congrArg WedgeCan4.piC h).trans (WedgeCan4.piC_coordsFull _))
  have hg' : IsLQGGood γ (E1.fromC (CoordsFull.coordsFull x.1)) :=
    (WedgeGood.isLQGGood_congr_coords hc).1 hg
  have hq := Factorization.qAreaMeasure_congr (CoordsFull.avgReg_congr_full h) γ
  show (if IsLQGGood γ (E1.fromC (CoordsFull.coordsFull x.1)) then
    qAreaMeasure γ (E1.fromC (CoordsFull.coordsFull x.1)) else 0) = _
  rw [if_pos hg', ← hq]

/-- **Measurability of the read zip-up data**, given measurability of the read scale. -/
theorem measurable_phiFull {γ t : ℝ} {G : Set E6.FullData} {F : E6.FullData → ℝ × (ℝ → ℝ)}
    (hR : LenDrvReading γ t G F) (hsc : Measurable (scF γ F)) : Measurable (phiFull γ F) := by
  obtain ⟨-, hT, hW, -⟩ := hR
  have hψ := measurable_psiZ hT hW
  have hψd := measurable_log_deriv_psiZ revInvLogDerivMeasStmt_holds hT hW
  obtain ⟨hdat, -⟩ := g4SurrogateZipDataMeasStmt_holds γ (fun d : E6.FullData => E1.fromC d.1.1)
    (psiZ F) (scF γ F) measurable_fromC_data' hψ hψd hsc
  refine hdat.prodMk (measurable_pi_iff.2 fun s => ?_)
  have hu : Measurable fun d : E6.FullData => scF γ F d ^ 2 * (s : ℝ) :=
    (hsc.pow_const 2).mul_const _
  unfold zipDrvOut
  refine Measurable.ite (measurableSet_le hu hT) ?_ ?_
  · exact ((hW.comp (measurable_id.prodMk (hT.sub hu))).sub
      (hW.comp (measurable_id.prodMk hT))).div hsc
  · exact ((measurable_extDrv.comp (measurable_id.prodMk (hu.sub hT))).sub
      (hW.comp (measurable_id.prodMk hT))).div hsc

/-- **The zip-up is read by `phiFull`** (deterministic). -/
theorem offData_zipLenA_eq {γ t : ℝ} (ht : 0 < t) {G : Set E6.FullData}
    {F : E6.FullData → ℝ × (ℝ → ℝ)} (hR : LenDrvReading γ t G F) {x : AreaConfig}
    (hc : Continuous x.drv) (h0 : x.drv 0 = 0) (hG : cfgData x.toPair ∈ G)
    (hg : IsLQGGood γ x.fld) (ha : x.area = qAreaMeasure γ x.fld) :
    offData (zipLenA γ t x).toPair = D74.maskSel (phiFull γ F (cfgData x.toPair)) := by
  set d := cfgData x.toPair with hd
  obtain ⟨hL, hT, hrem⟩ := hR.2.2.2 x.toPair hG
  have hsp := lenWeldDriver_spec (⟨_, hL⟩ : ∃ p, IsLenWeldingDriver γ x.fld t p)
  obtain ⟨hTe, hWe⟩ := isLenWeldingDriver_unique_of_good hL hT hrem _ _ hsp hL
  set T := (F d).1 with hTdef
  set W := (F d).2 with hWdef
  have hWc : Continuous W := hL.2.1
  have hW0 : W 0 = 0 := hL.2.2.1
  have hEq : EqOn (lenWeldDriver γ x.fld t).2 W (Icc 0 T) := by
    intro s hs
    exact hWe s (by rw [hTe]; exact hs)
  -- the zip-up along the chosen driver is the zip-up along the read driver
  have hZ : zipLenA γ t x = canonAConfig γ (zipWeldUpA γ T W x) := by
    rw [zipLenA_of_nonneg ht.le]
    show canonAConfig γ (zipWeldUpA γ (lenWeldDriver γ x.fld t).1 (lenWeldDriver γ x.fld t).2 x) = _
    rw [hTe]
    have e1 := zipWeldUp_congr (γ := γ) hT.le hEq x.toPair
    have e2 : revMap (lenWeldDriver γ x.fld t).2 T = revMap W T :=
      funext fun z => ReverseFlow.revMap_congr_drive z hEq
    simp only [zipWeldUpA, e1, e2]
  -- the scale
  have hmap : (x.area.restrict H).map (revMap W T) =
      ((muD γ d).restrict H).map fun z => fR F (d, z) := by
    rw [muD_cfgData (x := x.toPair) hg]
    change _ = Measure.map _ ((qAreaMeasure γ x.fld).restrict H)
    rw [← ha]
    refine Measure.map_congr ?_
    refine (ae_restrict_iff' isOpen_H.measurableSet).2 (ae_of_all _ fun z hz => ?_)
    have hz' : 0 < z.im := hz
    simp only [fR, if_pos hz']
    rw [ReverseFlow.revMap_congr_drive z (sclDrv_drvPath_eqOn hT hWc hW0).symm]
    exact revMap_sclDrv hT hz'
  set a := areaScale ((x.area.restrict H).map (revMap W T)) with hadef
  have hsc : scF γ F d = a := by rw [hadef, hmap]; rfl
  -- the field
  have hfld : (canonAConfig γ (zipWeldUpA γ T W x)).fld =
      canonicalData γ d (psiZ F d) (scF γ F d) := by
    rw [hsc]
    have hz := zipField_eq_zipFieldData γ x.toPair (T, W)
    rw [psiZ_eq_of_mem hR hG]
    show rescale (coordChange x.fld (revMapInv W T) (Qc γ)) (Qc γ) a =
      coordChange (zipFieldData γ d (revMapInv W T)) (fun w => (a : ℂ) * w) (Qc γ)
    rw [← hz]
    rfl
  -- the driver
  have hdrv : ∀ s : ℝ, (canonAConfig γ (zipWeldUpA γ T W x)).drv s =
      (if a ^ 2 * max s 0 ≤ T then W (T - max (a ^ 2 * max s 0) 0) - W T
        else x.drv (a ^ 2 * max s 0 - T) - W T) / a := fun s => rfl
  have hcont : Continuous (canonAConfig γ (zipWeldUpA γ T W x)).drv := by
    rw [show (canonAConfig γ (zipWeldUpA γ T W x)).drv = fun s =>
      (if a ^ 2 * max s 0 ≤ T then W (T - max (a ^ 2 * max s 0) 0) - W T
        else x.drv (a ^ 2 * max s 0 - T) - W T) / a from funext hdrv]
    refine Continuous.div_const ?_ _
    refine Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const
      fun s hs => ?_
    rw [hs, max_eq_left hT.le, sub_self, hW0, h0]
  have hzero : (canonAConfig γ (zipWeldUpA γ T W x)).drv 0 = 0 := by
    rw [hdrv]
    have hT0 : a ^ 2 * max (0 : ℝ) 0 ≤ T := by simp [hT.le]
    rw [if_pos hT0]
    simp
  rw [hZ]
  have hm := D74.maskSel_cfgData (x := (canonAConfig γ (zipWeldUpA γ T W x)).toPair) hcont hzero
  refine (hm.symm.trans ?_)
  congr 1
  refine Prod.ext (by simp only [cfgData, AreaConfig.toPair, phiFull]; rw [hfld]) ?_
  funext s
  show (canonAConfig γ (zipWeldUpA γ T W x)).drv s = zipDrvOut T (scF γ F d) W d.2 s
  rw [hdrv, hsc]
  have hs : max (s : ℝ) 0 = s := max_eq_left s.2
  have hu : max (a ^ 2 * (s : ℝ)) 0 = a ^ 2 * s := max_eq_left (by positivity)
  simp only [zipDrvOut, hs, hu]
  split_ifs with h
  · rfl
  · rw [hd]
    show _ = (extDrv (fun t : ℝ≥0 => x.drv t) (a ^ 2 * s - T) - W T) / a
    rw [extDrv_eq hc (by linarith)]

end ZipFac
end R18
end QuantumZipper
