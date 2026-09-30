import QuantumZipper.Proofs.Thm18.RTMeas3Weld
import QuantumZipper.Proofs.Thm18.RTMeasArea
import QuantumZipper.Proofs.Thm18.R18ZipFacCore
import QuantumZipper.Proofs.Thm18.R18ZipFacScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS3, part 3: the zip-up of the pieces, read from the encoded data

The pieces version of D81's `ZipFac.phiFull` (R18ZipFacCore.lean): along the open-arc welding
driver read by `ZO` (RTMeas3Weld.lean), the zip-up `zipLenUpOA` of the pieces (weld, then rescale
by (1.8) with the transported area; Sheffield arXiv:1012.4797 p. 26) has masked data
`πd (maskSel (phiO …))`, where `phiO` is Borel: the zipped field via
`g4SurrogateZipDataMeasStmt_holds` with the pieces' field `readOffField`, the scale via
`measurable_areaScale_map` with the area of the pieces (`muO`, measurable on the Borel set `GA`
of `AreaCertD`, RTMeasArea.lean), and the driver `zipDrvOut`.

Own elementary bookkeeping, copied from `ZipFac.offData_zipLenA_eq`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm

/-- The welding driver read from the full data through the encoding. -/
def FO (ZO : RD → PathT) (d : E6.FullData) : ℝ × (ℝ → ℝ) :=
  ((ZO (encT d)).2, sclDrv (ZO (encT d)))

theorem measurable_FO1 {ZO : RD → PathT} (hZ : Measurable ZO) :
    Measurable fun d => (FO ZO d).1 :=
  measurable_snd.comp (hZ.comp measurable_encT)

theorem measurable_FO2 {ZO : RD → PathT} (hZ : Measurable ZO) :
    Measurable fun q : E6.FullData × ℝ => (FO ZO q.1).2 q.2 :=
  measurable_sclDrv_uncurry.comp ((hZ.comp (measurable_encT.comp measurable_fst)).prodMk
    measurable_snd)

theorem encT_liftπ {e : (ℕ → ℝ) × (ℝ≥0 → ℝ)} (hc : Continuous e.2) : encT (liftπ e) = encR e := by
  simp [encT, encR, liftπ, hc]

open Classical in
/-- The area of the pieces on `ℍ`, on the Borel set `GA`. -/
def muO (γ : ℝ) (GA : Set PX) (d : E6.FullData) : Measure ℂ :=
  if πd d ∈ GA then (areaOfData γ (dfull (πd d))).restrict H else 0

theorem measurable_muO (γ : ℝ) {GA : Set PX} (hGAm : MeasurableSet GA)
    (hGA : ∀ p ∈ GA, AreaGood γ (dfull p)) : Measurable (muO γ GA) := by
  classical
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have e : (fun d => muO γ GA d s) = fun d => ⨆ N : ℕ, areaN γ GA N (πd d) s := by
    funext d
    unfold muO areaN
    split_ifs with h
    · rw [Measure.restrict_apply hs]
      simp_rw [Measure.restrict_apply hs]
      rw [← Monotone.measure_iUnion (fun m n hmn => inter_subset_inter_right _
        (LQGMeas.hExh_mono hmn)), ← inter_iUnion]
      congr 1
      refine subset_antisymm (inter_subset_inter_right _ LQGMeas.H_subset_iUnion_hExh) ?_
      exact inter_subset_inter_right _ (iUnion_subset fun N z hz =>
        LQGMeas.hExhK_subset_H N (LQGMeas.hExh_subset_compact N hz))
    · simp
  rw [e]
  exact Measurable.iSup fun N => (Measure.measurable_coe hs).comp
    ((measurable_areaN γ hGAm hGA N).comp measurable_πd)

theorem muO_fin (γ : ℝ) {GA : Set PX} (hGA : ∀ p ∈ GA, AreaGood γ (dfull p)) (d : E6.FullData)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ H) : muO γ GA d K < ⊤ := by
  classical
  unfold muO
  split_ifs with h
  · exact (Measure.restrict_apply_le _ _).trans_lt ((hGA _ h).2 K hK hKH)
  · simp

/-- The scale of the zip-up of the pieces, read from the data. -/
def scO (γ : ℝ) (GA : Set PX) (ZO : RD → PathT) (d : E6.FullData) : ℝ :=
  areaScale (((muO γ GA d).restrict H).map fun z => ZipFac.fR (FO ZO) (d, z))

theorem measurable_fR_FO {ZO : RD → PathT} (hZ : Measurable ZO) :
    Measurable (ZipFac.fR (FO ZO)) := by
  have hp : Measurable fun q : E6.FullData × ℂ =>
      (((drvPath (FO ZO) q.1, (FO ZO q.1).1) : PathT), q.2) :=
    (((measurable_drvPath (measurable_FO1 hZ) (measurable_FO2 hZ)).comp measurable_fst).prodMk
      ((measurable_FO1 hZ).comp measurable_fst)).prodMk measurable_snd
  exact measurable_rvS_H.comp hp

theorem measurable_scO (γ : ℝ) {GA : Set PX} (hGAm : MeasurableSet GA)
    (hGA : ∀ p ∈ GA, AreaGood γ (dfull p)) {ZO : RD → PathT} (hZ : Measurable ZO) :
    Measurable (scO γ GA ZO) :=
  measurable_areaScale_map (measurable_muO γ hGAm hGA) (muO_fin γ hGA) (measurable_fR_FO hZ)

/-- The zipped pieces' data, read from the data. -/
def phiO (γ : ℝ) (GA : Set PX) (ZO : RD → PathT) (d : E6.FullData) : E6.FullData :=
  ((CoordsFull.coordsFull (coordChange (coordChange (readOffField d) (psiZ (FO ZO) d) (Qc γ))
      (fun w => (scO γ GA ZO d : ℂ) * w) (Qc γ)), fun _ => 0),
    fun s => zipDrvOut (FO ZO d).1 (scO γ GA ZO d) (FO ZO d).2 d.2 s)

theorem measurable_phiO (γ : ℝ) {GA : Set PX} (hGAm : MeasurableSet GA)
    (hGA : ∀ p ∈ GA, AreaGood γ (dfull p)) {ZO : RD → PathT} (hZ : Measurable ZO) :
    Measurable (phiO γ GA ZO) := by
  have hT := measurable_FO1 hZ
  have hW := measurable_FO2 hZ
  have hsc := measurable_scO γ hGAm hGA hZ
  have hψ := measurable_psiZ hT hW
  have hψd := measurable_log_deriv_psiZ revInvLogDerivMeasStmt_holds hT hW
  obtain ⟨hdat, -⟩ := g4SurrogateZipDataMeasStmt_holds γ (fun d : E6.FullData => readOffField d)
    (psiZ (FO ZO)) (scO γ GA ZO) measurable_readOffField hψ hψd hsc
  refine (hdat.fst.prodMk measurable_const).prodMk (measurable_pi_iff.2 fun s => ?_)
  have hu : Measurable fun d : E6.FullData => scO γ GA ZO d ^ 2 * (s : ℝ) :=
    (hsc.pow_const 2).mul_const _
  unfold zipDrvOut
  refine Measurable.ite (measurableSet_le hu hT) ?_ ?_
  · exact ((hW.comp (measurable_id.prodMk (hT.sub hu))).sub
      (hW.comp (measurable_id.prodMk hT))).div hsc
  · exact ((measurable_extDrv.comp (measurable_id.prodMk (hu.sub hT))).sub
      (hW.comp (measurable_id.prodMk hT))).div hsc

/-- **The zip-up of the pieces is read by `phiO`** (deterministic). -/
theorem encR_zipLenUpOA_eq {γ ℓ : ℝ} {GA : Set PX} {Good : Set PathT}
    (hgood : ∀ p ∈ Good, GoodP p) {ZO : RD → PathT} {e : (ℕ → ℝ) × (ℝ≥0 → ℝ)}
    (hc : Continuous e.2) (h0 : e.2 0 = 0) (hG : (encR e, ZO (encR e)) ∈ GamO γ ℓ Good)
    (hA : e ∈ GA) :
    encR (πdO (zipLenUpOA γ ℓ (configOfData γ (liftπ e)))) =
      encT' (πd (D74.maskSel (phiO γ GA ZO (liftπ e)))) := by
  classical
  set d := liftπ e with hd
  set x := configOfData γ d with hx
  set p := ZO (encR e) with hpdef
  have hFd : FO ZO d = (p.2, sclDrv p) := by
    simp only [FO, hd, encT_liftπ hc, hpdef]
  have hpG : p ∈ Good := hG.2.1
  obtain ⟨hT, hp0, hK, hrem⟩ := hgood p hpG
  have hL : IsLenWeldingDriverO γ x.fld ℓ (p.2, sclDrv p) := by
    have h := isLenWeldingDriverO_of_memO hgood hG
    have e1 : Xf (encR e) = x.fld := by
      show readOffField (dfull (decM (encR e))) = readOffField d
      rw [decM_encR hc]; rfl
    rw [e1] at h
    exact h
  have hsp : IsLenWeldingDriverO γ x.fld ℓ (lenWeldDriverO γ x.fld ℓ) :=
    Classical.epsilon_spec ⟨_, hL⟩
  obtain ⟨hTe, hWe⟩ := isLenWeldingDriverO_eq_of_good hL hT hrem hsp
  set T := p.2 with hTdef
  set W := sclDrv p with hWdef
  have hWc : Continuous W := continuous_sclDrv p
  have hW0 : W 0 = 0 := hp0
  have hEq : EqOn (lenWeldDriverO γ x.fld ℓ).2 W (Icc 0 T) := fun s hs => (hWe hs).symm
  have hZ : zipLenUpOA γ ℓ x = canonAConfig γ (zipWeldUpA γ T W x) := by
    unfold zipLenUpOA
    rw [hTe]
    have e1 := zipWeldUp_congr (γ := γ) hT.le hEq x.toPair
    have e2 : revMap (lenWeldDriverO γ x.fld ℓ).2 T = revMap W T :=
      funext fun z => ReverseFlow.revMap_congr_drive z hEq
    simp only [zipWeldUpA, e1, e2]
  have hxc : Continuous x.drv := continuous_drvOfData (d := liftπ e) hc
  have hx0 : x.drv 0 = 0 := by
    have h1 : x.drv 0 = e.2 ⟨max (0 : ℝ) 0, le_max_right _ _⟩ := rfl
    have h2 : (⟨max (0 : ℝ) 0, le_max_right _ _⟩ : ℝ≥0) = 0 := by ext; simp
    rw [h1, h2]; exact h0
  -- the scale
  have hFT : 0 < (FO ZO d).1 := by rw [hFd]; exact hT
  have hFW : Continuous (FO ZO d).2 := by rw [hFd]; exact hWc
  have hFW0 : (FO ZO d).2 0 = 0 := by rw [hFd]; exact hW0
  have hmap : (x.area.restrict H).map (revMap W T) =
      ((muO γ GA d).restrict H).map fun z => ZipFac.fR (FO ZO) (d, z) := by
    have hmu : muO γ GA d = (areaOfData γ d).restrict H := by
      unfold muO; rw [if_pos (show πd d ∈ GA from hA)]; rfl
    rw [hmu, Measure.restrict_restrict isOpen_H.measurableSet, inter_self]
    refine Measure.map_congr ?_
    refine (ae_restrict_iff' isOpen_H.measurableSet).2 (ae_of_all _ fun z hz => ?_)
    have hz' : 0 < z.im := hz
    simp only [ZipFac.fR, if_pos hz']
    have eT : (FO ZO d).1 = T := by rw [hFd]
    have eW : (FO ZO d).2 = W := by rw [hFd]
    rw [← eW, ← eT]
    rw [ReverseFlow.revMap_congr_drive z (sclDrv_drvPath_eqOn hFT hFW hFW0).symm]
    exact revMap_sclDrv (p := (drvPath (FO ZO) d, (FO ZO d).1)) hFT hz'
  set a := areaScale ((x.area.restrict H).map (revMap W T)) with hadef
  have hsc : scO γ GA ZO d = a := by rw [hadef, hmap]; rfl
  -- the field
  have hψ : psiZ (FO ZO) d = revMapInv W T := by
    rw [psiZ_eq hFT hFW hFW0, hFd]
  have hfld : (canonAConfig γ (zipWeldUpA γ T W x)).fld =
      coordChange (coordChange (readOffField d) (psiZ (FO ZO) d) (Qc γ))
        (fun w => (scO γ GA ZO d : ℂ) * w) (Qc γ) := by
    rw [hsc, hψ]
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
    rw [hs, max_eq_left hT.le, sub_self, hW0, hx0]
  have hzero : (canonAConfig γ (zipWeldUpA γ T W x)).drv 0 = 0 := by
    rw [hdrv]
    have hT0 : a ^ 2 * max (0 : ℝ) 0 ≤ T := by simp [hT.le]
    rw [if_pos hT0]
    simp
  set out := canonAConfig γ (zipWeldUpA γ T W x) with hout
  have hπc : Continuous (πdO out).2 := hcont.comp continuous_subtype_val
  rw [hZ, encR_eq_encT' hπc]
  congr 1
  have hm := D74.maskSel_cfgData (x := out.toPair) hcont hzero
  show πd (offData out.toPair) = _
  rw [show offData out.toPair = D74.maskSel (cfgData out.toPair) from hm.symm]
  show πd (D74.maskSel ((CoordsFull.coordsFull out.fld, fun ρ : TestFun H => pairRaw out.fld ρ.1),
    fun s : ℝ≥0 => out.drv s)) = _
  rw [πd_maskSel_congr (p' := fun _ => 0)]
  unfold phiO
  rw [hfld]
  congr 3
  funext s
  show out.drv s = zipDrvOut (FO ZO d).1 (scO γ GA ZO d) (FO ZO d).2 d.2 s
  rw [hdrv, hsc, hFd]
  have hs : max (s : ℝ) 0 = s := max_eq_left s.2
  have hu : max (a ^ 2 * (s : ℝ)) 0 = a ^ 2 * s := max_eq_left (by positivity)
  simp only [zipDrvOut, hs, hu]
  split_ifs with h
  · rfl
  · show _ = (extDrv e.2 (a ^ 2 * s - T) - W T) / a
    have he : e.2 = fun t : ℝ≥0 => x.drv t := by
      funext t
      show e.2 t = e.2 ⟨max (t : ℝ) 0, le_max_right _ _⟩
      have h3 : (⟨max (t : ℝ) 0, le_max_right _ _⟩ : ℝ≥0) = t := by ext; simp
      rw [h3]
    rw [he, extDrv_eq hxc (by linarith)]

end RTMeas
end R18
end QuantumZipper
