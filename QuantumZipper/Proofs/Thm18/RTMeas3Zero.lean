import QuantumZipper.Proofs.Thm18.RTMeas3Pos
import QuantumZipper.Proofs.Zipper.Cor15Partial

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS3, part 6: `UpPiecesReadStmt` for `ℓ = 0`, and the node

For `ℓ = 0` the open-arc welding point is `0`, so every open-arc length-welding driver has time
`0` (`lenWeldDriverO_zero_time`) and one exists (`(0, 0)`); the zip-up by time `0` is the identity
on `ℍ` (`revMap_zero_eq`, `revMapInv_zero_eqOn`), so `zipLenUpOA γ 0` only regularizes the field
at the circles, rescales by (1.8) with the area of the pieces, and rescales the driver. Its masked
data are read by an explicit Borel map (`evalReg` at the circles, `rescCoord`, the area scale of
`muO`, `extDrv`). With `upPiecesRead_pos` this proves `UpPiecesReadStmt`.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm Thm18Asm.G4Core

theorem lenWeldPointO_zero (γ : ℝ) (x : FieldSample) : lenWeldPointO γ x 0 = 0 := by
  unfold lenWeldPointO
  have e : {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal 0 ≤ openArcLen γ x s 0} = Iic 0 := by
    ext s; simp
  rw [e, csSup_Iic]

theorem weldHomRO_zero (γ : ℝ) (x : FieldSample) : weldHomRO γ x 0 = 0 := by
  unfold weldHomRO
  have h0 : openArcLen γ x 0 0 = 0 := by
    unfold openArcLen; simp
  have e : {r : ℝ | 0 ≤ r ∧ openArcLen γ x 0 0 ≤ openArcLen γ x 0 r} = Ici 0 := by
    ext r; simp [h0]
  rw [e, csInf_Ici]

theorem isLenWeldingDriverO_zero (γ : ℝ) (x : FieldSample) :
    IsLenWeldingDriverO γ x 0 (0, fun _ => 0) := by
  refine ⟨le_rfl, continuous_const, rfl, Or.inl rfl, ?_, fun s hs => ?_⟩
  · rw [B5.zeroMinus_zero_time continuous_const rfl, lenWeldPointO_zero]
  · have hs0 : s = 0 := by
      rw [B5.zeroMinus_zero_time continuous_const rfl] at hs
      exact le_antisymm hs.2 hs.1
    subst hs0
    rw [Thm14WeldingData.weldingHom_zero, weldHomRO_zero]

theorem lenWeldDriverO_zero_time {γ : ℝ} {x : FieldSample} {q : ℝ × (ℝ → ℝ)}
    (hq : IsLenWeldingDriverO γ x 0 q) : q.1 = 0 := by
  obtain ⟨hq1, hqc, hq00, hqK', hqz, -⟩ := hq
  rcases hq1.lt_or_eq with h | h
  · exfalso
    have hqK : IsSimpleCurveHull (revHull q.2 q.1) := hqK'.resolve_left h.ne'
    obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory q.2 hqc hq00 q.1 h hqK
    have hneg : zeroMinus q.2 q.1 < 0 :=
      (WeldingConsistency.car_basic hqc h hF (WeldingConsistency.simpleCurveHull_nonempty hqK)).1
    rw [hqz, lenWeldPointO_zero] at hneg
    exact lt_irrefl _ hneg
  · exact h.symm

/-- The zip-up by length `0` along the zero driver. -/
theorem zipLenUpOA_zero_eq (γ : ℝ) (x : AreaConfig) :
    zipLenUpOA γ 0 x = canonAConfig γ (zipWeldUpA γ 0 (fun _ => 0) x) := by
  have hsp : IsLenWeldingDriverO γ x.fld 0 (lenWeldDriverO γ x.fld 0) :=
    Classical.epsilon_spec ⟨_, isLenWeldingDriverO_zero γ x.fld⟩
  have hT := lenWeldDriverO_zero_time hsp
  have hW0 : (lenWeldDriverO γ x.fld 0).2 0 = 0 := hsp.2.2.1
  have hEq : EqOn (lenWeldDriverO γ x.fld 0).2 (fun _ => (0 : ℝ)) (Icc 0 0) := by
    intro s hs
    have : s = 0 := le_antisymm hs.2 hs.1
    subst this; exact hW0
  unfold zipLenUpOA
  rw [hT]
  have e1 := zipWeldUp_congr (γ := γ) le_rfl hEq x.toPair
  have e2 : revMap (lenWeldDriverO γ x.fld 0).2 0 = revMap (fun _ => (0 : ℝ)) 0 :=
    funext fun z => ReverseFlow.revMap_congr_drive z hEq
  simp only [zipWeldUpA, e1, e2]

theorem coordsFull_coordChange_zero (γ : ℝ) (X : FieldSample) :
    CoordsFull.coordsFull (coordChange X (revMapInv (fun _ => (0 : ℝ)) 0) (Qc γ)) =
      fun i => evalReg X (circI i) := by
  funext i
  have hid := Cor15Partial.revMapInv_zero_eqOn (W := fun _ => (0 : ℝ)) continuous_const rfl
  have hmap : (circI i).map (revMapInv (fun _ => (0 : ℝ)) 0) = circI i := by
    rw [Measure.map_congr (g := id) ?_, Measure.map_id]
    filter_upwards [ae_mem_H_circI i] with z hz using hid hz
  have hlog : ∫ z, Real.log ‖deriv (revMapInv (fun _ => (0 : ℝ)) 0) z‖ ∂circI i = 0 := by
    refine (integral_congr_ae ?_).trans (integral_zero ℂ ℝ)
    filter_upwards [ae_mem_H_circI i] with z hz
    have hd : deriv (revMapInv (fun _ => (0 : ℝ)) 0) z = 1 := by
      rw [Filter.EventuallyEq.deriv_eq (f := id) ?_, deriv_id]
      filter_upwards [isOpen_H.mem_nhds hz] with w hw using hid hw
    simp [hd]
  show evalReg X ((circI i).map _) + Qc γ * _ = _
  rw [hmap, hlog, mul_zero, add_zero]

/-- The circle coordinates of the regularized pieces' field. -/
def c0 (y : RD) : ℕ → ℝ := fun i => evalReg (Xf y) (circI i)

theorem measurable_c0 : Measurable c0 :=
  measurable_pi_iff.2 fun i => (measurable_evalReg (circI i)).comp measurable_Xf

/-- The area scale of the pieces, read from the data. -/
def sc0 (γ : ℝ) (GA : Set PX) (d : E6.FullData) : ℝ :=
  areaScale (((muO γ GA d).restrict H).map fun z => (fun q : E6.FullData × ℂ => q.2) (d, z))

theorem measurable_sc0 (γ : ℝ) {GA : Set PX} (hGAm : MeasurableSet GA)
    (hGA : ∀ p ∈ GA, AreaGood γ (dfull p)) : Measurable (sc0 γ GA) :=
  measurable_areaScale_map (measurable_muO γ hGAm hGA) (muO_fin γ hGA) measurable_snd

/-- The driver of the zip-up by length `0`, read from the data. -/
def drv0 (a : ℝ) (e : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  (if a ^ 2 * (s : ℝ) ≤ 0 then 0 else extDrv e (a ^ 2 * s)) / a

/-- The reader for `ℓ = 0`. -/
def g0 (γ : ℝ) (GA : Set PX) (y : RD) : RD :=
  encT' (πd (D74.maskSel ((rescCoord γ (ESM.fromCoords (c0 y)) (sc0 γ GA (dfull (decM y))),
    fun _ => 0), fun s => drv0 (sc0 γ GA (dfull (decM y))) (decM y).2 s)))

theorem measurable_g0 (γ : ℝ) {GA : Set PX} (hGAm : MeasurableSet GA)
    (hGA : ∀ p ∈ GA, AreaGood γ (dfull p)) : Measurable (g0 γ GA) := by
  have hsc : Measurable fun y : RD => sc0 γ GA (dfull (decM y)) :=
    (measurable_sc0 γ hGAm hGA).comp (measurable_dfull.comp measurable_decM)
  have hco : Measurable fun y : RD => rescCoord γ (ESM.fromCoords (c0 y)) (sc0 γ GA (dfull (decM y))) :=
    Measurable.comp (g := fun r : FieldSample × ℝ => rescCoord γ r.1 r.2)
      (f := fun y : RD => (ESM.fromCoords (c0 y), sc0 γ GA (dfull (decM y))))
      (measurable_rescCoord γ) ((ESM.measurable_fromCoords measurable_c0).prodMk hsc)
  have hdr : Measurable fun y : RD => fun s : ℝ≥0 => drv0 (sc0 γ GA (dfull (decM y))) (decM y).2 s := by
    refine measurable_pi_iff.2 fun s => ?_
    have hu : Measurable fun y : RD => sc0 γ GA (dfull (decM y)) ^ 2 * (s : ℝ) :=
      (hsc.pow_const 2).mul_const _
    have hext : Measurable fun y : RD => extDrv (decM y).2 (sc0 γ GA (dfull (decM y)) ^ 2 * s) :=
      measurable_extDrv.comp (f := fun y : RD => (dfull (decM y), sc0 γ GA (dfull (decM y)) ^ 2 * s))
        ((measurable_dfull.comp measurable_decM).prodMk hu)
    exact (Measurable.ite (measurableSet_le hu measurable_const) measurable_const hext).div hsc
  exact measurable_encT'.comp (measurable_πd.comp (D74.measurable_maskSel.comp
    ((hco.prodMk measurable_const).prodMk hdr)))

theorem ratNN_zero : ratNN 0 = 0 := by
  apply NNReal.eq; show max ((0 : ℚ) : ℝ) 0 = 0; simp

/-- **The zip-up by length `0` of the pieces is read by `g0`** (deterministic). -/
theorem g0_eq {γ : ℝ} {GA : Set PX} {e : (ℕ → ℝ) × (ℝ≥0 → ℝ)} (hc : Continuous e.2)
    (h0 : e.2 0 = 0) (hA : e ∈ GA) :
    g0 γ GA (encR e) = encR (πdO (zipLenUpOA γ 0 (configOfData γ (liftπ e)))) := by
  set d := liftπ e with hd
  set x := configOfData γ d with hx
  set W : ℝ → ℝ := fun _ => 0 with hW
  have hxc : Continuous x.drv := continuous_drvOfData (d := liftπ e) hc
  have hx0 : x.drv 0 = 0 := by
    have h1 : x.drv 0 = e.2 ⟨max (0 : ℝ) 0, le_max_right _ _⟩ := rfl
    have h2 : (⟨max (0 : ℝ) 0, le_max_right _ _⟩ : ℝ≥0) = 0 := by ext; simp
    rw [h1, h2]; exact h0
  rw [zipLenUpOA_zero_eq]
  -- the scale
  have hmap : (x.area.restrict H).map (revMap W 0) = (muO γ GA d).restrict H := by
    have hmu : muO γ GA d = (areaOfData γ d).restrict H := by
      unfold muO; rw [if_pos (show πd d ∈ GA from hA)]; rfl
    rw [hmu, Measure.restrict_restrict isOpen_H.measurableSet, inter_self,
      Measure.map_congr (g := id) ?_, Measure.map_id]
    · rfl
    refine (ae_restrict_iff' isOpen_H.measurableSet).2 (ae_of_all _ fun z hz => ?_)
    exact CharFun.revMap_zero_eq continuous_const rfl hz
  set a := areaScale ((x.area.restrict H).map (revMap W 0)) with hadef
  have hsc : sc0 γ GA d = a := by
    rw [hadef, hmap]
    unfold sc0
    rw [Measure.map_id']
  -- the driver
  have hdrv : ∀ s : ℝ, (canonAConfig γ (zipWeldUpA γ 0 W x)).drv s =
      (if a ^ 2 * max s 0 ≤ 0 then W (0 - max (a ^ 2 * max s 0) 0) - W 0
        else x.drv (a ^ 2 * max s 0 - 0) - W 0) / a := fun s => rfl
  have hcont : Continuous (canonAConfig γ (zipWeldUpA γ 0 W x)).drv := by
    rw [show (canonAConfig γ (zipWeldUpA γ 0 W x)).drv = fun s =>
      (if a ^ 2 * max s 0 ≤ 0 then W (0 - max (a ^ 2 * max s 0) 0) - W 0
        else x.drv (a ^ 2 * max s 0 - 0) - W 0) / a from funext hdrv]
    refine Continuous.div_const ?_ _
    refine Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const
      fun s hs => ?_
    rw [hs, sub_self, hx0]
    simp [hW]
  have hzero : (canonAConfig γ (zipWeldUpA γ 0 W x)).drv 0 = 0 := by
    rw [hdrv]; simp [hW]
  set out := canonAConfig γ (zipWeldUpA γ 0 W x) with hout
  have hπc : Continuous (πdO out).2 := hcont.comp continuous_subtype_val
  rw [encR_eq_encT' hπc]
  unfold g0
  congr 1
  have hm := D74.maskSel_cfgData (x := out.toPair) hcont hzero
  show _ = πd (offData out.toPair)
  rw [show offData out.toPair = D74.maskSel (cfgData out.toPair) from hm.symm]
  show _ = πd (D74.maskSel ((CoordsFull.coordsFull out.fld,
    fun ρ : TestFun H => pairRaw out.fld ρ.1), fun s : ℝ≥0 => out.drv s))
  rw [πd_maskSel_congr (p := fun ρ : TestFun H => pairRaw out.fld ρ.1) (p' := fun _ => 0)]
  have hdec : decM (encR e) = e := decM_encR hc
  have hdd : dfull (decM (encR e)) = d := by rw [hdec]; rfl
  have hc0 : c0 (encR e) = CoordsFull.coordsFull (coordChange x.fld (revMapInv W 0) (Qc γ)) := by
    rw [coordsFull_coordChange_zero]
    funext i
    show evalReg (readOffField (dfull (decM (encR e)))) (circI i) = _
    rw [hdd]
    rfl
  have hfld : rescCoord γ (ESM.fromCoords (c0 (encR e))) (sc0 γ GA (dfull (decM (encR e)))) =
      CoordsFull.coordsFull out.fld := by
    rw [hdd, hsc, hc0, rescCoord_congr γ (F1.coordsFull_fromCoords_coordsFull _)]
    rfl
  have hdr : ∀ s : ℝ≥0, drv0 (sc0 γ GA (dfull (decM (encR e)))) (decM (encR e)).2 s =
      out.drv s := by
    intro s
    rw [hdd, hsc, hdec, hdrv]
    have hs : max (s : ℝ) 0 = s := max_eq_left s.2
    have hu : max (a ^ 2 * (s : ℝ)) 0 = a ^ 2 * s := max_eq_left (by positivity)
    simp only [drv0, hs, hu, hW, sub_zero]
    split_ifs with h
    · simp
    · have he : e.2 = fun t : ℝ≥0 => x.drv t := by
        funext t
        show e.2 t = e.2 ⟨max (t : ℝ) 0, le_max_right _ _⟩
        have h3 : (⟨max (t : ℝ) 0, le_max_right _ _⟩ : ℝ≥0) = t := by ext; simp
        rw [h3]
      rw [he, extDrv_eq hxc (by positivity)]
  exact congrArg (fun z => πd (D74.maskSel z)) (Prod.ext (Prod.ext hfld rfl) (funext hdr))

/-- **`UpPiecesReadStmt` holds.** -/
theorem upPiecesReadStmt_holds : UpPiecesReadStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ
  rcases hℓ.lt_or_eq with hpos | hzero
  · exact upPiecesRead_pos γ P B Y hS hIn ℓ hpos
  subst hzero
  obtain ⟨GA, hGAm, hGA, hGAae⟩ := areaRegStmt_holds γ P B Y hS hIn
  have hGA' : ∀ p ∈ GA, AreaGood γ (dfull p) := fun p hp => hGA (dfull p) hp
  refine ⟨{y : RD | y.2 = 1 ∧ y.1.2 0 = 0 ∧ decM y ∈ GA}, g0 γ GA, ?_, measurable_g0 γ hGAm hGA',
    fun e hc he => ?_, ?_⟩
  · exact (measurableSet_eq_fun measurable_snd measurable_const).inter
      ((measurableSet_eq_fun ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_fst))
        measurable_const).inter (measurable_decM hGAm))
  · obtain ⟨-, h0, hA⟩ := he
    have h0' : e.2 0 = 0 := by
      have : (encR e).1.2 0 = e.2 (ratNN 0) := rfl
      rw [this, ratNN_zero] at h0; exact h0
    rw [decM_encR hc] at hA
    have hz : zipRead γ 0 e = zipLenUpOA γ 0 (configOfData γ (liftπ e)) := by
      unfold zipRead; rw [if_pos le_rfl]
    rw [hz]
    exact g0_eq hc h0' hA
  · filter_upwards [D74.ae_wedgeConfig_snd_good hS, hGAae] with ω hW hA
    set e := πdO (wedgeAConfig γ B Y ω) with hedef
    have hc : Continuous e.2 := hW.1.comp continuous_subtype_val
    refine ⟨by simp [encR, hc], ?_, by rw [decM_encR hc]; exact hA⟩
    show e.2 (ratNN 0) = 0
    rw [ratNN_zero]; exact hW.2

end RTMeas
end R18
end QuantumZipper
