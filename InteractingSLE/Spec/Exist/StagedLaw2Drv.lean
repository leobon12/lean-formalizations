/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw2Thr
import InteractingSLE.Spec.Exist.StagedLawStmt

/-!
# The stopped driver of a launch: alive events and the forward map are measurable

Packet PROVE-STAGEDLAW2. `ExplState.launch` runs a piece with the stopped driver `Wr = W_{· ∧ stop}` up to
`T = stop = min t ζ`. This file connects `Wr` to the continuous drivers read from records (`LocalExt.histDrv`), which
are measurable, and derives:

* `stopDrv`, `stopTime`, `recDrv`; `recDrv_eq_stopDrv` (on a good record); `isDrvGood_of_isForwardSol` (a solution up
  to the stop forces a good record);
* `measurable_fwdMap_stop`, `measurableSet_alive_stop`: the forward map at the stop, and the alive event at the stop,
  at a measurable starting point;
* `measurableSet_aliveBefore`: the event "alive at every time before the stop" at a measurable starting point (the
  first half of `hit`), through the records stopped at rational times;
* `measurable_posInf`, `measurable_negSup`: the infimum of the positive and the supremum of the negative alive points
  of a measurable family of order-shaped sets;
* `isRealFlow_stop`, `isUpDown_before`: the shapes of the alive sets.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper Staged

/-! ### The stopped driver and the record driver -/

section Drv

variable {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The stopped driver of a launch on the real line (`ExplState.launch`'s `Wr`). -/
def stopDrv (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : ℝ → ℝ := fun x => (retOf t e).1 x.toNNReal

/-- The time of a launch (`0` for an infinite stop). -/
def stopTime (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : ℝ := ((min t e.2).toNNReal : ℝ)

/-- The driver read from the record of the piece stopped at `min t ζ` (continuous for every record). -/
def recDrv (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : ℝ → ℝ :=
  fun x => LocalExt.histDrv (recHist (recOf t e)) x.toNNReal

theorem stopTime_nonneg (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : 0 ≤ stopTime t e := NNReal.coe_nonneg _

theorem continuous_recDrv (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : Continuous (recDrv t e) :=
  (LocalExt.continuous_histDrv _).comp continuous_real_toNNReal

theorem recDrv_zero (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : recDrv t e 0 = 0 := by
  simp only [recDrv, Real.toNNReal_zero, LocalExt.histDrv_zero]

theorem stopDrv_zero (he : IsRegularDriver e) (t : ℝ≥0∞) : stopDrv t e 0 = 0 := by
  simp only [stopDrv, retOf, Real.toNNReal_zero, ENNReal.coe_zero, zero_le, min_eq_left, ENNReal.toNNReal_zero]
  exact he.2.1

theorem recDrv_eq_stopDrv (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (recOf t e))) :
    recDrv t e = stopDrv t e :=
  funext fun x => histDrv_recHist he hg x.toNNReal

/-- The stopped driver is constant from the stop on. -/
theorem retOf_eq_min (hfin : min t e.2 ≠ ⊤) (r : ℝ≥0) :
    (retOf t e).1 r = (retOf t e).1 (min r (min t e.2).toNNReal) := by
  change e.1 (min (r : ℝ≥0∞) (min t e.2)).toNNReal = e.1 (min ((min r (min t e.2).toNNReal : ℝ≥0) : ℝ≥0∞)
    (min t e.2)).toNNReal
  rw [ENNReal.coe_min, ENNReal.coe_toNNReal hfin, min_assoc, min_self]

theorem readRec_sample (q : ℚ≥0) : ((recHist (recOf t e)).2 q).1 = (retOf t e).1 (q : ℝ≥0) := by
  change (retOf t e).1 (((q : ℚ) : ℝ)).toNNReal = _
  rw [toNNReal_ratCast_nnrat]

/-- **A solution up to the stop forces a good record** (the stopped driver is then continuous on `[0, T]`). -/
theorem isDrvGood_of_isForwardSol (he : IsRegularDriver e) (hfin : min t e.2 ≠ ⊤) {y : ℂ} {u : ℝ → ℂ}
    (hu : IsForwardSol (stopDrv t e) y (stopTime t e) u) : LocalExt.IsDrvGood (recHist (recOf t e)) := by
  have hc := continuousOn_driver_of_isForwardSol hu
  refine LocalExt.isDrvGood_of_continuousOn (g := (retOf t e).1) (T := (min t e.2).toNNReal) ?_ (fun q => ?_) ?_
  · have hmaps : MapsTo (fun x : ℝ≥0 => (x : ℝ)) (Icc 0 (min t e.2).toNNReal) (Icc 0 (stopTime t e)) :=
      fun x hx => ⟨x.coe_nonneg, NNReal.coe_le_coe.2 hx.2⟩
    have h := hc.comp NNReal.continuous_coe.continuousOn hmaps
    refine h.congr fun x _ => ?_
    simp only [Function.comp, stopDrv, Real.toNNReal_coe]
  · rw [readRec_sample, retOf_eq_min hfin]
  · change e.1 (min ((0 : ℝ≥0) : ℝ≥0∞) (min t e.2)).toNNReal = 0
    rw [ENNReal.coe_zero, min_eq_left (zero_le (a := min _ _)), ENNReal.toNNReal_zero]
    exact he.2.1

/-- **The record of a piece stopped before its lifetime is good, and its driver is the original one up to the
stop.** -/
theorem isDrvGood_recOf_of_lt (he : IsRegularDriver e) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < e.2) :
    LocalExt.IsDrvGood (recHist (recOf (r : ℝ≥0∞) e)) := by
  have hmin : min (r : ℝ≥0∞) e.2 = r := min_eq_left hr.le
  refine LocalExt.isDrvGood_of_continuousOn (g := (retOf (r : ℝ≥0∞) e).1) (T := r) ?_ (fun q => ?_) ?_
  · have heq : EqOn (retOf (r : ℝ≥0∞) e).1 e.1 (Icc 0 r) := fun x hx => by
      change e.1 (min (x : ℝ≥0∞) (min (r : ℝ≥0∞) e.2)).toNNReal = e.1 x
      rw [hmin, min_eq_left (ENNReal.coe_le_coe.2 hx.2), ENNReal.toNNReal_coe]
    refine (he.1.mono fun x (hx : x ∈ Icc 0 r) => ?_).congr heq
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 hx.2) hr
  · rw [readRec_sample]
    have h := retOf_eq_min (t := (r : ℝ≥0∞)) (e := e) (by rw [hmin]; exact ENNReal.coe_ne_top) q
    rw [h, hmin, ENNReal.toNNReal_coe]
  · change e.1 (min ((0 : ℝ≥0) : ℝ≥0∞) (min (r : ℝ≥0∞) e.2)).toNNReal = 0
    rw [ENNReal.coe_zero, min_eq_left (zero_le (a := min _ _)), ENNReal.toNNReal_zero]
    exact he.2.1

/-- Before the stop, the stopped driver is the record driver of the piece stopped at a rational time. -/
theorem eqOn_stopDrv_recDrv (he : IsRegularDriver e) {r : ℝ≥0} (hr : (r : ℝ) < stopTime t e) :
    EqOn (stopDrv t e) (recDrv (r : ℝ≥0∞) e) (Icc 0 (r : ℝ)) := by
  have hrs : (r : ℝ≥0∞) < min t e.2 := by
    by_contra h
    push Not at h
    have hfin : min t e.2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h
    have : (min t e.2).toNNReal ≤ r := (ENNReal.toNNReal_le_toNNReal hfin ENNReal.coe_ne_top).2 h
    exact absurd hr (not_lt.2 (by simpa [stopTime] using NNReal.coe_le_coe.2 this))
  have hre : (r : ℝ≥0∞) < e.2 := hrs.trans_le (min_le_right _ _)
  intro x hx
  have hx' : ((x.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ r := by
    rw [ENNReal.coe_le_coe, Real.toNNReal_le_iff_le_coe]; exact hx.2
  rw [recDrv, histDrv_recHist he (isDrvGood_recOf_of_lt he hre)]
  change e.1 (min _ (min t e.2)).toNNReal = e.1 (min _ (min (r : ℝ≥0∞) e.2)).toNNReal
  rw [min_eq_left (hx'.trans hrs.le), min_eq_left (show (r : ℝ≥0∞) ≤ e.2 from hre.le), min_eq_left hx']

end Drv


/-! ### Shapes of the alive sets -/

section Shape

variable {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- On a good record the alive set at the stop has the real flow structure. -/
theorem isRealFlow_stop (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (recOf t e))) :
    IsRealFlow (fun y : ℝ => ∃ u, IsForwardSol (stopDrv t e) (y : ℂ) (stopTime t e) u)
      (fun y => (fwdMap (stopDrv t e) (stopTime t e) y).re) := by
  rw [← recDrv_eq_stopDrv he hg]
  exact isRealFlow_fwd (continuous_recDrv t e) (recDrv_zero t e) (stopTime_nonneg t e)

/-- On a bad record nothing is alive at a finite stop. -/
theorem not_alive_stop (he : IsRegularDriver e) (hfin : min t e.2 ≠ ⊤)
    (hg : ¬ LocalExt.IsDrvGood (recHist (recOf t e))) (y : ℂ) :
    ¬ ∃ u, IsForwardSol (stopDrv t e) y (stopTime t e) u :=
  fun ⟨_, hu⟩ => hg (isDrvGood_of_isForwardSol he hfin hu)

theorem exists_rat_btwn_nnrat {s T : ℝ} (hs : 0 ≤ s) (hsT : s < T) : ∃ r : ℚ≥0, s < (r : ℝ) ∧ (r : ℝ) < T := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hsT
  have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hs.trans hq1.le
  refine ⟨⟨q, hq0⟩, ?_, ?_⟩ <;> rw [NNRat.cast_mk] <;> assumption

/-- Alive at every time before the stop, read at rational times through the records. -/
theorem aliveBefore_iff (he : IsRegularDriver e) (y : ℂ) :
    (∀ s < stopTime t e, ∃ u, IsForwardSol (stopDrv t e) y s u) ↔
      ∀ r : ℚ≥0, (r : ℝ) < stopTime t e → ∃ u, IsForwardSol (recDrv ((r : ℝ≥0) : ℝ≥0∞) e) y (r : ℝ) u := by
  constructor
  · intro H r hr
    obtain ⟨u, hu⟩ := H r hr
    exact ⟨u, (Ito.isForwardSol_iff_of_eqOn (eqOn_stopDrv_recDrv (r := (r : ℝ≥0)) he hr) u).1 hu⟩
  · intro H s hs
    rcases lt_or_ge s 0 with hs0 | hs0
    · refine ⟨fun _ => 0, ?_, fun r hr => absurd (hr.1.trans hr.2) (not_le.2 hs0)⟩
      rw [Icc_eq_empty (not_le.2 hs0)]; exact continuousOn_empty _
    · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn_nnrat hs0 hs
      obtain ⟨u, hu⟩ := H r hr2
      have hu' := (Ito.isForwardSol_iff_of_eqOn (eqOn_stopDrv_recDrv (r := (r : ℝ≥0)) he hr2) u).2 hu
      exact ⟨u, isForwardSol_restrict hu' hs0 hr1.le⟩

/-- The alive-before set has the order shape. -/
theorem isUpDown_aliveBefore (he : IsRegularDriver e) :
    IsUpDown fun y : ℝ => ∀ s < stopTime t e, ∃ u, IsForwardSol (stopDrv t e) (y : ℂ) s u := by
  simp_rw [aliveBefore_iff he]
  have h : ∀ r : ℚ≥0, IsUpDown fun y : ℝ => ∃ u, IsForwardSol (recDrv ((r : ℝ≥0) : ℝ≥0∞) e) (y : ℂ) (r : ℝ) u :=
    fun r => (isRealFlow_fwd (continuous_recDrv _ e) (recDrv_zero _ e) (by positivity)).isUpDown
  exact ⟨fun q y hq hqy H r hr => (h r).1 q y hq hqy (H r hr),
    fun q y hyq hq0 H r hr => (h r).2 q y hyq hq0 (H r hr)⟩

/-- `0` is not alive before a positive stop. -/
theorem not_aliveBefore_zero (he : IsRegularDriver e) (hT : 0 < stopTime t e) :
    ¬ ∀ s < stopTime t e, ∃ u, IsForwardSol (stopDrv t e) ((0 : ℝ) : ℂ) s u := fun H => by
  have h := exists_isForwardSol_zero_iff.1 (H 0 hT)
  rw [stopDrv_zero he] at h
  simp at h

end Shape

/-! ### Measurability -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (t : ℝ≥0∞)

theorem measurable_stopTime (hD : Measurable D) : Measurable fun ω => stopTime t (D ω) :=
  measurable_coe_nnreal_real.comp ((measurable_const.min (measurable_snd.comp hD)).ennreal_toNNReal)

theorem measurableSet_good (hD : Measurable D) (hreg : ∀ ω, IsRegularDriver (D ω)) :
    MeasurableSet {ω | LocalExt.IsDrvGood (recHist (recOf t (D ω)))} :=
  (measurable_recHist.comp (measurable_recOf hD hreg t)) LocalExt.measurableSet_isDrvGood

theorem measurable_recDrv_apply (hD : Measurable D) (hreg : ∀ ω, IsRegularDriver (D ω)) (x : ℝ) :
    Measurable fun ω => recDrv t (D ω) x :=
  (LocalExt.measurable_histDrv_apply x.toNNReal).comp (measurable_recHist.comp (measurable_recOf hD hreg t))

theorem measurableSet_stop_top (hD : Measurable D) : MeasurableSet {ω | min t (D ω).2 = ⊤} :=
  measurableSet_eq_fun (measurable_const.min (measurable_snd.comp hD)) measurable_const

/-- **The forward map at the stop and the alive event at the stop are measurable** (measurable starting point). -/
theorem measurable_fwdMap_stop (hD : Measurable D) (hreg : ∀ ω, IsRegularDriver (D ω)) {y : Ω → ℂ}
    (hy : Measurable y) :
    Measurable (fun ω => fwdMap (stopDrv t (D ω)) (stopTime t (D ω)) (y ω)) ∧
      MeasurableSet {ω | ∃ u, IsForwardSol (stopDrv t (D ω)) (y ω) (stopTime t (D ω)) u} := by
  classical
  have hP := measurable_fwdMap_param (W := fun ω => recDrv t (D ω)) (fun ω => continuous_recDrv t (D ω))
    (measurable_recDrv_apply t hD hreg) (fun ω => recDrv_zero t (D ω)) (measurable_stopTime t hD)
    (fun ω => stopTime_nonneg t (D ω)) hy
  set G := {ω | LocalExt.IsDrvGood (recHist (recOf t (D ω)))} with hG
  set F := {ω | min t (D ω).2 = ⊤} with hF
  have hGm := measurableSet_good t hD hreg
  have hFm := measurableSet_stop_top t hD
  have hT0 : ∀ ω ∈ F, stopTime t (D ω) = 0 := fun ω hω => by
    simp only [stopTime, show min t (D ω).2 = ⊤ from hω, ENNReal.toNNReal_top, NNReal.coe_zero]
  constructor
  · have e : (fun ω => fwdMap (stopDrv t (D ω)) (stopTime t (D ω)) (y ω)) =
        F.piecewise y (G.piecewise (fun ω => fwdMap (recDrv t (D ω)) (stopTime t (D ω)) (y ω)) fun _ => 0) := by
      funext ω
      by_cases hωF : ω ∈ F
      · rw [piecewise_eq_of_mem _ _ _ hωF, hT0 ω hωF, fwdMap_zero_time (stopDrv_zero (hreg ω) t)]
      · rw [piecewise_eq_of_notMem _ _ _ hωF]
        by_cases hωG : ω ∈ G
        · rw [piecewise_eq_of_mem _ _ _ hωG, recDrv_eq_stopDrv (hreg ω) hωG]
        · rw [piecewise_eq_of_notMem _ _ _ hωG]
          exact fwdMap_of_not (not_alive_stop (hreg ω) hωF hωG _)
    rw [e]
    exact hy.piecewise hFm (hP.1.piecewise hGm measurable_const)
  · have e : {ω | ∃ u, IsForwardSol (stopDrv t (D ω)) (y ω) (stopTime t (D ω)) u} =
        (F ∩ {ω | y ω ≠ 0}) ∪ (Fᶜ ∩ G ∩ {ω | ∃ u, IsForwardSol (recDrv t (D ω)) (y ω) (stopTime t (D ω)) u}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
      by_cases hωF : ω ∈ F
      · rw [hT0 ω hωF, exists_isForwardSol_zero_iff, stopDrv_zero (hreg ω)]
        simp [hωF]
      · by_cases hωG : ω ∈ G
        · rw [recDrv_eq_stopDrv (hreg ω) hωG]
          simp [hωF, hωG]
        · simp only [hωF, hωG, false_and, and_false, or_false, iff_false]
          exact not_alive_stop (hreg ω) hωF hωG _
    rw [e]
    exact (hFm.inter (measurableSet_eq_fun hy measurable_const).compl).union ((hFm.compl.inter hGm).inter hP.2)

/-- **The event "alive at every time before the stop" is measurable** (measurable starting point). -/
theorem measurableSet_aliveBefore (hD : Measurable D) (hreg : ∀ ω, IsRegularDriver (D ω)) {y : Ω → ℂ}
    (hy : Measurable y) :
    MeasurableSet {ω | ∀ s < stopTime t (D ω), ∃ u, IsForwardSol (stopDrv t (D ω)) (y ω) s u} := by
  have e : {ω | ∀ s < stopTime t (D ω), ∃ u, IsForwardSol (stopDrv t (D ω)) (y ω) s u} =
      ⋂ r : ℚ≥0, ({ω | (r : ℝ) < stopTime t (D ω)}ᶜ ∪
        {ω | ∃ u, IsForwardSol (recDrv ((r : ℝ≥0) : ℝ≥0∞) (D ω)) (y ω) ((r : ℝ≥0) : ℝ) u}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, not_lt]
    rw [aliveBefore_iff (hreg ω)]
    refine forall_congr' fun r => ?_
    constructor
    · intro h
      by_cases hr : (r : ℝ) < stopTime t (D ω)
      · exact Or.inr (h hr)
      · exact Or.inl (not_lt.1 hr)
    · rintro (h | h) hr
      · exact absurd hr (not_lt.2 h)
      · exact h
  rw [e]
  refine MeasurableSet.iInter fun r => ?_
  refine ((measurableSet_lt measurable_const (measurable_stopTime t hD)).compl).union ?_
  exact (measurable_fwdMap_param (W := fun ω => recDrv ((r : ℝ≥0) : ℝ≥0∞) (D ω))
    (fun ω => continuous_recDrv _ (D ω)) (measurable_recDrv_apply _ hD hreg) (fun ω => recDrv_zero _ (D ω))
    measurable_const (fun _ => NNReal.coe_nonneg _) hy).2

/-- **The infimum of the positive alive points is measurable.** -/
theorem measurable_posInf {A : Ω → ℝ → Prop} (hA : ∀ ω, IsUpDown (A ω))
    (hAm : ∀ q : ℚ, MeasurableSet {ω | A ω q}) : Measurable fun ω => posInf (A ω) := by
  refine measurable_of_Iio fun c => ?_
  show MeasurableSet {ω | posInf (A ω) < c}
  set P := ⋃ q : ℚ, ({ω | (0 : ℝ) < q} ∩ {ω | A ω q}) with hP
  have hPm : MeasurableSet P := MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter (hAm q)
  have e : {ω | posInf (A ω) < c} =
      (P ∩ ⋃ q : ℚ, ({ω | (0 : ℝ) < q ∧ (q : ℝ) < c} ∩ {ω | A ω q})) ∪ (Pᶜ ∩ {ω | (0 : ℝ) < c}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_iUnion, mem_compl_iff, hP]
    by_cases hne : {y | 0 < y ∧ A ω y}.Nonempty
    · have hPω : ∃ q : ℚ, (0 : ℝ) < q ∧ A ω q := by
        obtain ⟨z, hz0, hzA⟩ := hne
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show z < z + 1 by linarith)
        exact ⟨q, hz0.trans hq1, (hA ω).1 z q hz0 hq1 hzA⟩
      have hb : BddBelow {y | 0 < y ∧ A ω y} := ⟨0, fun _ hy => hy.1.le⟩
      constructor
      · intro h
        obtain ⟨z, ⟨hz0, hzA⟩, hzc⟩ := exists_lt_of_csInf_lt hne h
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hzc
        exact Or.inl ⟨by simpa using hPω, q, ⟨hz0.trans hq1, hq2⟩, (hA ω).1 z q hz0 hq1 hzA⟩
      · rintro (⟨-, q, ⟨hq0, hqc⟩, hqA⟩ | ⟨hn, -⟩)
        · exact (csInf_le hb ⟨hq0, hqA⟩).trans_lt hqc
        · exact absurd (by simpa using hPω) hn
    · have hemp : {y | 0 < y ∧ A ω y} = ∅ := not_nonempty_iff_eq_empty.1 hne
      have hPω : ¬ ∃ q : ℚ, (0 : ℝ) < q ∧ A ω q := fun ⟨q, hq0, hqA⟩ => hne ⟨q, hq0, hqA⟩
      simp only [posInf, hemp, Real.sInf_empty]
      constructor
      · intro h; exact Or.inr ⟨by simpa using hPω, h⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd (by simpa using h) hPω
        · exact h
  rw [e]
  exact (hPm.inter (MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter (hAm q))).union
    (hPm.compl.inter (MeasurableSet.const _))

/-- **The supremum of the negative alive points is measurable.** -/
theorem measurable_negSup {A : Ω → ℝ → Prop} (hA : ∀ ω, IsUpDown (A ω))
    (hAm : ∀ q : ℚ, MeasurableSet {ω | A ω q}) : Measurable fun ω => negSup (A ω) := by
  have hA' : ∀ ω, IsUpDown fun y => A ω (-y) := fun ω =>
    ⟨fun q y hq hqy h => by simpa using (hA ω).2 (-q) (-y) (by linarith) (by linarith) h,
      fun q y hyq hq h => by simpa using (hA ω).1 (-q) (-y) (by linarith) (by linarith) h⟩
  have hAm' : ∀ q : ℚ, MeasurableSet {ω | A ω (-(q : ℝ))} := fun q => by
    have := hAm (-q); simpa using this
  have h := measurable_posInf hA' hAm'
  have e : (fun ω => negSup (A ω)) = fun ω => -posInf (fun y => A ω (-y)) := by
    funext ω
    have hs : {y | y < 0 ∧ A ω y} = -{y | 0 < y ∧ A ω (-y)} := by
      ext y; simp only [mem_ofPred_eq, Set.mem_neg]; constructor <;> rintro ⟨h1, h2⟩ <;>
        refine ⟨by linarith, by simpa using h2⟩
    rw [negSup, posInf, hs, Real.sSup_neg]
  rw [e]
  exact h.neg

end Meas

end StagedLaw

end Exist

end InteractingSLE
