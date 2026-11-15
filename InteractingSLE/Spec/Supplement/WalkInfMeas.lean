/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkInfHull
import InteractingSLE.Spec.Supplement.WalkSideDom
import InteractingSLE.Spec.Sec7.LocalExtOChart
import InteractingSLE.Spec.Exist.StagedLaw3Rand
import InteractingSLE.Spec.Restart.ChartMeasHull
import InteractingSLE.GFF.LocalSets.AbsContConformal

/-!
# Measurable random charts: recentring and composition with record charts

Packet PROVE-T14-WALKINF, for input (B) of `WalkSide.walkPrefixSideStatement_of_prefix`. A random chart `c : Ω → Chart`
is **measurable for `m`** (`IsMeasChart m c`) when it is conformal with a continuous harmonic lift at every sample and
its domain events, masked forward maps, closed-disc events and masked lifts are `m`-measurable — exactly the
hypotheses of `Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw`. Here:

* `IsMeasChart.measurableSet_dom_prod`: the domain is jointly measurable (closed rational discs, the domain is open);
* `IsMeasChart.measurable_fwd_prod`, `IsMeasChart.measurable_lift_prod`: the masked forward map and lift are jointly
  measurable (Carathéodory: measurable at each point, continuous on the open domain; dyadic approximations);
* `IsMeasChart.recenter`: closed under recentring by an `m`-measurable real amount.

Deterministic and measurability facts only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull fwdMap tamedZ drive)

namespace InteractingSLE.Theorem14.WalkInf

/-! ### Measurable random charts -/

section Def

variable {Ω : Type*}

/-- **A measurable random chart** for the σ-algebra `m`: conformal with a continuous harmonic lift at every sample;
domain events, masked forward maps, closed-disc events and masked lifts measurable for `m`. -/
def IsMeasChart (m : MeasurableSpace Ω) (c : Ω → Chart) : Prop :=
  (∀ ω, (c ω).IsConformal) ∧ (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
    (∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) ∧
    (∀ z, MeasurableSet[m] {ω | z ∈ (c ω).dom}) ∧
    (∀ z, Measurable[m] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
    (∀ (z : ℂ) (ε : ℝ), MeasurableSet[m] {ω | closedBall z ε ⊆ (c ω).dom}) ∧
    (∀ z, Measurable[m] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))

end Def

/-! ### Dyadic grid points -/

section Grid

/-- The lower-left corner of the dyadic square of level `n` and index `k`. -/
def gridPt (n : ℕ) (k : ℤ × ℤ) : ℂ := ⟨(k.1 : ℝ) / 2 ^ n, (k.2 : ℝ) / 2 ^ n⟩

theorem gridPt_mem (n : ℕ) (k : ℤ × ℤ) : gridPt n k ∈ Restart.dyadicSquare n k := by
  have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [gridPt] <;> rw [mul_div_cancel₀ _ hp] <;> linarith

theorem measurable_dyadicIndexOf (n : ℕ) : Measurable (Restart.dyadicIndexOf n) :=
  (Int.measurable_floor.comp (measurable_const.mul Complex.measurable_re)).prodMk
    (Int.measurable_floor.comp (measurable_const.mul Complex.measurable_im))

theorem norm_sub_gridPt_le (n : ℕ) (z : ℂ) : ‖z - gridPt n (Restart.dyadicIndexOf n z)‖ ≤ 2 / 2 ^ n :=
  Restart.norm_sub_le_of_mem_dyadicSquare (Restart.mem_dyadicSquare_indexOf n z) (gridPt_mem n _)

theorem tendsto_gridPt (z : ℂ) : Tendsto (fun n => gridPt n (Restart.dyadicIndexOf n z)) atTop (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun n : ℕ => 2 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul 2
    simpa [div_eq_mul_inv, one_div, inv_pow] using this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h2
  rw [norm_sub_rev]
  exact norm_sub_gridPt_le n z

end Grid

/-! ### Joint measurability -/

section Joint

variable {Ω : Type*} {m : MeasurableSpace Ω} {c : Ω → Chart}

/-- **The domain of a measurable random chart is jointly measurable.** -/
theorem IsMeasChart.measurableSet_dom_prod (hc : IsMeasChart m c) :
    MeasurableSet[m.prod inferInstance] {p : Ω × ℂ | p.2 ∈ (c p.1).dom} := by
  let _ : MeasurableSpace Ω := m
  have e : {p : Ω × ℂ | p.2 ∈ (c p.1).dom} =
      ⋃ (q : ℚ × ℚ) (r : ℚ), {ω | closedBall (WangWu.ratPt q.1 q.2) (r : ℝ) ⊆ (c ω).dom} ×ˢ
        closedBall (WangWu.ratPt q.1 q.2) (r : ℝ) := by
    ext ⟨ω, z⟩
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod]
    constructor
    · intro hz
      obtain ⟨x, ⟨q, rfl⟩, r, hzx, hsub⟩ :=
        WalkLaw.exists_closedBall_subset_of_mem WangWu.denseRange_ratPt (c ω).dom.isOpen hz
      exact ⟨q, r, hsub, hzx⟩
    · rintro ⟨q, r, hsub, hz⟩
      exact hsub hz
  rw [e]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun r =>
    (hc.2.2.2.2.2.1 _ _).prod measurableSet_closedBall

/-- **Carathéodory on an open random domain.** A function measurable at each point on the domain events and continuous
on the (open) domains is jointly measurable, masked by the domain. -/
theorem measurable_masked_prod {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (hc : IsMeasChart m c) {F : Ω → ℂ → E}
    (hFm : ∀ z, Measurable[m] ({ω | z ∈ (c ω).dom}.indicator fun ω => F ω z))
    (hFc : ∀ ω, ContinuousOn (F ω) (c ω).dom) :
    Measurable[m.prod inferInstance]
      ({p : Ω × ℂ | p.2 ∈ (c p.1).dom}.indicator fun p => F p.1 p.2) := by
  let _ : MeasurableSpace Ω := m
  set J := {p : Ω × ℂ | p.2 ∈ (c p.1).dom} with hJ
  have hJm : MeasurableSet J := hc.measurableSet_dom_prod
  -- the approximations
  set f : ℕ → Ω × ℂ → E := fun n p => J.indicator (fun p =>
    {ω | gridPt n (Restart.dyadicIndexOf n p.2) ∈ (c ω).dom}.indicator
      (fun ω => F ω (gridPt n (Restart.dyadicIndexOf n p.2))) p.1) p with hf
  have hfm : ∀ n, Measurable (f n) := by
    intro n
    have hA : Measurable fun p : Ω × (ℤ × ℤ) =>
        {ω | gridPt n p.2 ∈ (c ω).dom}.indicator (fun ω => F ω (gridPt n p.2)) p.1 :=
      measurable_from_prod_countable_left fun k => hFm (gridPt n k)
    have hB : Measurable fun p : Ω × ℂ => (p.1, Restart.dyadicIndexOf n p.2) :=
      measurable_fst.prodMk ((measurable_dyadicIndexOf n).comp measurable_snd)
    exact (hA.comp hB).indicator hJm
  refine measurable_of_tendsto_metrizable hfm (tendsto_pi_nhds.2 fun p => ?_)
  by_cases hp : p ∈ J
  · have hpd : p.2 ∈ (c p.1).dom := hp
    rw [indicator_of_mem hp]
    have hev : ∀ᶠ n in atTop, gridPt n (Restart.dyadicIndexOf n p.2) ∈ (c p.1).dom :=
      (tendsto_gridPt p.2).eventually ((c p.1).dom.isOpen.mem_nhds hpd)
    have hlim : Tendsto (fun n => F p.1 (gridPt n (Restart.dyadicIndexOf n p.2))) atTop (𝓝 (F p.1 p.2)) :=
      ((hFc p.1).continuousAt ((c p.1).dom.isOpen.mem_nhds hpd)).tendsto.comp (tendsto_gridPt p.2)
    refine hlim.congr' ?_
    filter_upwards [hev] with n hn
    simp only [hf, indicator_of_mem hp]
    rw [indicator_of_mem (show p.1 ∈ {ω | gridPt n (Restart.dyadicIndexOf n p.2) ∈ (c ω).dom} from hn)]
  · rw [indicator_of_notMem hp]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    simp only [hf, indicator_of_notMem hp]

/-- The masked forward map of a measurable random chart is jointly measurable. -/
theorem IsMeasChart.measurable_fwd_prod (hc : IsMeasChart m c) :
    Measurable[m.prod inferInstance] ({p : Ω × ℂ | p.2 ∈ (c p.1).dom}.indicator fun p => (c p.1).1 p.2) :=
  measurable_masked_prod hc hc.2.2.2.2.1 fun ω => (hc.1 ω).differentiableOn_fwd.continuousOn

/-- The masked lift of a measurable random chart is jointly measurable. -/
theorem IsMeasChart.measurable_lift_prod (hc : IsMeasChart m c) :
    Measurable[m.prod inferInstance] ({p : Ω × ℂ | p.2 ∈ (c p.1).dom}.indicator fun p => (c p.1).2.2 p.2) :=
  measurable_masked_prod hc hc.2.2.2.2.2.2 hc.2.1

/-- **Domain events at a random point.** -/
theorem IsMeasChart.measurableSet_mem_dom_of_measurable (hc : IsMeasChart m c) {Y : Ω → ℂ}
    (hY : Measurable[m] Y) : MeasurableSet[m] {ω | Y ω ∈ (c ω).dom} := by
  let _ : MeasurableSpace Ω := m
  exact hc.measurableSet_dom_prod.preimage (measurable_id.prodMk hY)

/-- **The masked forward map at a random point.** -/
theorem IsMeasChart.measurable_fwd_of_measurable (hc : IsMeasChart m c) {Y : Ω → ℂ} (hY : Measurable[m] Y) :
    Measurable[m] ({ω | Y ω ∈ (c ω).dom}.indicator fun ω => (c ω).1 (Y ω)) := by
  let _ : MeasurableSpace Ω := m
  have h := hc.measurable_fwd_prod.comp (measurable_id.prodMk hY)
  convert h using 1
  funext ω
  by_cases hω : Y ω ∈ (c ω).dom
  · simp only [Function.comp_apply, id, indicator_of_mem (show (ω, Y ω) ∈ {p : Ω × ℂ | p.2 ∈ (c p.1).dom} from hω),
      indicator_of_mem (show ω ∈ {ω | Y ω ∈ (c ω).dom} from hω)]
  · simp only [Function.comp_apply, id,
      indicator_of_notMem (show (ω, Y ω) ∉ {p : Ω × ℂ | p.2 ∈ (c p.1).dom} from hω),
      indicator_of_notMem (show ω ∉ {ω | Y ω ∈ (c ω).dom} from hω)]

/-- **The masked lift at a random point.** -/
theorem IsMeasChart.measurable_lift_of_measurable (hc : IsMeasChart m c) {Y : Ω → ℂ} (hY : Measurable[m] Y) :
    Measurable[m] ({ω | Y ω ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 (Y ω)) := by
  let _ : MeasurableSpace Ω := m
  have h := hc.measurable_lift_prod.comp (measurable_id.prodMk hY)
  convert h using 1
  funext ω
  by_cases hω : Y ω ∈ (c ω).dom
  · simp only [Function.comp_apply, id, indicator_of_mem (show (ω, Y ω) ∈ {p : Ω × ℂ | p.2 ∈ (c p.1).dom} from hω),
      indicator_of_mem (show ω ∈ {ω | Y ω ∈ (c ω).dom} from hω)]
  · simp only [Function.comp_apply, id,
      indicator_of_notMem (show (ω, Y ω) ∉ {p : Ω × ℂ | p.2 ∈ (c p.1).dom} from hω),
      indicator_of_notMem (show ω ∉ {ω | Y ω ∈ (c ω).dom} from hω)]

end Joint

/-! ### Recentring -/

section Recenter

variable {Ω : Type*} {m : MeasurableSpace Ω} {c : Ω → Chart}

/-- **Recentring by a measurable amount keeps a random chart measurable.** -/
theorem IsMeasChart.recenter (hc : IsMeasChart m c) {a : Ω → ℝ} (ha : Measurable[m] a) :
    IsMeasChart m fun ω => (c ω).recenter (a ω) := by
  let _ : MeasurableSpace Ω := m
  obtain ⟨hconf, hlc, hharm, hdom, hfwd, hcb, hlift⟩ := hc
  have hd : ∀ ω, ((c ω).recenter (a ω)).dom = (c ω).dom := fun ω => WalkSide.dom_recenter _ _
  refine ⟨fun ω => (hconf ω).recenter _, fun ω => ?_, fun ω => ?_, fun z => ?_, fun z => ?_, fun z ε => ?_,
    fun z => ?_⟩
  · rw [hd]; exact hlc ω
  · rw [hd]; exact hharm ω
  · simp only [hd]; exact hdom z
  · simp only [hd]
    have e : ({ω | z ∈ (c ω).dom}.indicator fun ω => ((c ω).recenter (a ω)).1 z) =
        ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z) -
          {ω | z ∈ (c ω).dom}.indicator fun ω => ((a ω : ℝ) : ℂ) := by
      funext ω
      by_cases hω : ω ∈ {ω | z ∈ (c ω).dom}
      · simp only [Pi.sub_apply, indicator_of_mem hω]; rfl
      · simp only [Pi.sub_apply, indicator_of_notMem hω, sub_zero]
    rw [e]
    exact (hfwd z).sub ((Complex.measurable_ofReal.comp ha).indicator (hdom z))
  · simp only [hd]; exact hcb z ε
  · simp only [hd]; exact hlift z

end Recenter

/-! ### Record charts -/

section Rec

open Exist.StagedLaw

/-- The driver of the record chart. -/
abbrev recV (t : ℝ≥0) (r : RecData) : ℝ := LocalExt.histDrv (recHist r) t

theorem continuous_recV (r : RecData) : Continuous fun t => recV t r := LocalExt.continuous_histDrv _

theorem recV_zero (r : RecData) : recV 0 r = 0 := LocalExt.histDrv_zero _

theorem measurable_recV (t : ℝ≥0) : Measurable (recV t) :=
  (LocalExt.measurable_histDrv_apply t).comp measurable_recHist

theorem drive_recV (r : RecData) : drive 1 (fun t r => recV t r) r = Ito.rpath (fun t => recV t r) := by
  funext s
  simp [drive, Ito.rpath]

theorem recChart_eq (r : RecData) :
    recChart r = Chart.id.loewner (Ito.rpath (fun t => recV t r)) (LocalExt.histTime (recHist r) : ℝ) := rfl

theorem continuous_rpath_recV (r : RecData) : Continuous (Ito.rpath (fun t => recV t r)) :=
  (continuous_recV r).comp continuous_real_toNNReal

theorem rpath_recV_zero (r : RecData) : Ito.rpath (fun t => recV t r) 0 = 0 := by
  simp [Ito.rpath, recV_zero]

/-- The domain of a record chart is `ℍ` minus the hull of its driver. -/
theorem mem_dom_recChart_iff (r : RecData) {z : ℂ} :
    z ∈ (recChart r).dom ↔ z ∈ H \ fwdHull (Ito.rpath (fun t => recV t r)) (LocalExt.histTime (recHist r) : ℝ) := by
  rw [recChart_eq]
  exact Sec5.CrossCond.Staged.mem_dom_loewner_iff_mem_diff_hull (continuous_rpath_recV r) (rpath_recV_zero r)
    (LocalExt.histTime (recHist r)).coe_nonneg

/-- The tamed flow of the record driver at a random point is measurable. -/
theorem measurable_tamedZ_recV {Ω : Type*} {m : MeasurableSpace Ω} {r : Ω → RecData} (hr : Measurable[m] r)
    {Y : Ω → ℂ} (hY : Measurable[m] Y) {c : ℝ} (hc : 0 < c) {s : ℝ} (hs : 0 ≤ s) :
    Measurable[m] fun ω => tamedZ (Ito.rpath (fun t => recV t (r ω))) c (Y ω) s := by
  let _ : MeasurableSpace Ω := m
  have h := (QuantumZipper.measurable_tamed_drive (Ω := Ω) 1 hc (fun t ω => recV t (r ω))
    (fun ω => continuous_recV (r ω)) hs (fun t _ => (measurable_recV t).comp hr)).1
  have h2 := h.comp (hY.prodMk measurable_id)
  convert h2 using 1
  funext ω
  have e : drive 1 (fun t ω => recV t (r ω)) ω = Ito.rpath (fun t => recV t (r ω)) := by
    funext x
    simp [drive, Ito.rpath]
  simp only [Function.comp_apply, id, e]

/-- **Closed-disc events of the record chart.** -/
theorem measurableSet_closedBall_subset_dom_recChart (z : ℂ) (ε : ℝ) :
    MeasurableSet {r : RecData | closedBall z ε ⊆ (recChart r).dom} := by
  rcases lt_or_ge ε 0 with hε | hε
  · have : closedBall z ε = ∅ := closedBall_eq_empty.2 hε
    simp only [this, empty_subset, ofPred_true, MeasurableSet.univ]
  rcases hε.eq_or_lt with rfl | hε
  · simp only [closedBall_zero, singleton_subset_iff]
    exact measurableSet_mem_dom_recChart z
  rcases lt_or_ge ε z.im with hz | hz
  · have e : {r : RecData | closedBall z ε ⊆ (recChart r).dom} =
        {r | ∃ k : ℕ, ∀ y : ℚ × ℚ, Sec7.Coding.ratPt y ∈ closedBall z ε → ∀ s : ℚ, 0 ≤ (s : ℝ) →
          (s : ℝ) ≤ (LocalExt.histTime (recHist r) : ℝ) →
          2 * (1 / ((k : ℝ) + 1)) ≤
            (tamedZ (Ito.rpath (fun t => recV t r)) (1 / ((k : ℝ) + 1)) (Sec7.Coding.ratPt y) s).im} := by
      ext r
      simp only [mem_ofPred_eq]
      rw [← Sec7.Lemma72D.disjoint_closedBall_fwdHull_iff_real (continuous_rpath_recV r)
        (LocalExt.histTime (recHist r)).coe_nonneg hε hz]
      constructor
      · intro hB
        exact Set.disjoint_left.2 fun y hy hK => ((mem_dom_recChart_iff r).1 (hB hy)).2 hK
      · intro hd y hy
        exact (mem_dom_recChart_iff r).2 ⟨Sec7.Coding.closedBall_subset_H hz hy, Set.disjoint_left.1 hd hy⟩
    rw [e]
    have htm : Measurable fun r : RecData => (LocalExt.histTime (recHist r) : ℝ) :=
      measurable_coe_nnreal_real.comp (LocalExt.measurable_histTime.comp measurable_recHist)
    refine measurableSet_setOfPred.2 (Measurable.exists fun k => Measurable.forall fun y =>
      Measurable.imp measurable_const (Measurable.forall fun s => ?_))
    by_cases hs : 0 ≤ (s : ℝ)
    · have hm := measurable_tamedZ_recV (m := inferInstance) measurable_id measurable_const
        (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity) hs (Y := fun _ => Sec7.Coding.ratPt y)
      refine Measurable.imp measurable_const (Measurable.imp ?_ ?_)
      · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const htm)
      · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (Complex.measurable_im.comp hm))
    · have e2 : (fun r : RecData => 0 ≤ (s : ℝ) → (s : ℝ) ≤ (LocalExt.histTime (recHist r) : ℝ) →
          2 * (1 / ((k : ℝ) + 1)) ≤
            (tamedZ (Ito.rpath (fun t => recV t r)) (1 / ((k : ℝ) + 1)) (Sec7.Coding.ratPt y) s).im) =
          fun _ => True := by
        funext r
        simp only [hs, false_implies]
      rw [e2]
      exact measurable_const
  · have hB : ∀ r : RecData, ¬ closedBall z ε ⊆ (recChart r).dom := by
      intro r hB
      have hmem : z - (ε : ℂ) * Complex.I ∈ closedBall z ε := by
        rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
          mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      have := ((mem_dom_recChart_iff r).1 (hB hmem)).1
      simp only [H, mem_ofPred_eq, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero] at this
      linarith
    have : {r : RecData | closedBall z ε ⊆ (recChart r).dom} = ∅ := by
      ext r
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact hB r
    rw [this]
    exact MeasurableSet.empty

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **A record chart of a measurable record is a measurable random chart.** -/
theorem isMeasChart_recChart {r : Ω → RecData} (hr : Measurable[m] r) : IsMeasChart m fun ω => recChart (r ω) := by
  let _ : MeasurableSpace Ω := m
  refine ⟨fun ω => isConformal_recChart _, fun ω => LocalExt.continuousOn_lift_histChart _,
    fun ω => LocalExt.harmonicOnNhd_lift_histChart _, fun z => hr (measurableSet_mem_dom_recChart z),
    fun z => (measurable_indicator_fwd_recChart z).comp hr,
    fun z ε => hr (measurableSet_closedBall_subset_dom_recChart z ε),
    fun z => (measurable_indicator_lift_recChart z).comp hr⟩

end Rec

/-! ### Composition with a record chart -/

section Trans

open Exist.StagedLaw

/-- **The domain of a composite of conformal charts.** -/
theorem mem_dom_trans_iff {c d : Chart} (hc : c.IsConformal) (hd : d.IsConformal) {z : ℂ} :
    z ∈ (c.trans d).dom ↔ z ∈ c.dom ∧ c.1 z ∈ d.dom := by
  rw [(hc.trans hd).mem_dom_iff, hc.mem_dom_iff, hd.mem_dom_iff]
  simp only [Chart.trans_fst, Chart.trans_inv]
  constructor
  · rintro ⟨hH, heq⟩
    have hu : d.2.1 (d.1 (c.1 z)) ∈ H := hd.2.1 hH
    have hcz : c.1 z = d.2.1 (d.1 (c.1 z)) := by
      conv_lhs => rw [← heq]
      exact hc.2.2 _ hu
    refine ⟨⟨hcz ▸ hu, ?_⟩, hH, hcz.symm⟩
    conv_lhs => rw [hcz]
    exact heq
  · rintro ⟨⟨-, hcinv⟩, hdH, hdinv⟩
    exact ⟨hdH, by rw [hdinv, hcinv]⟩

variable {Ω : Type*} {m : MeasurableSpace Ω} {c : Ω → Chart}

/-- **Composing with the record chart of a measurable record keeps a random chart measurable.** -/
theorem IsMeasChart.trans_recChart (hc : IsMeasChart m c) {r : Ω → RecData} (hr : Measurable[m] r) :
    IsMeasChart m fun ω => (c ω).trans (recChart (r ω)) := by
  let _ : MeasurableSpace Ω := m
  have hd := isMeasChart_recChart hr
  have hc' := hc
  obtain ⟨hconf, hlc, hharm, hdom, hfwd, hcb, hlift⟩ := hc'
  have hmem : ∀ ω z, z ∈ ((c ω).trans (recChart (r ω))).dom ↔
      z ∈ (c ω).dom ∧ (c ω).1 z ∈ (recChart (r ω)).dom := fun ω z =>
    mem_dom_trans_iff (hconf ω) (hd.1 ω)
  have hsub : ∀ ω, (((c ω).trans (recChart (r ω))).dom : Set ℂ) ⊆ (c ω).dom := fun ω z hz =>
    ((hmem ω z).1 hz).1
  have hmaps : ∀ ω, MapsTo (c ω).1 ((c ω).trans (recChart (r ω))).dom (recChart (r ω)).dom := fun ω z hz =>
    ((hmem ω z).1 hz).2
  -- the masked forward point
  set Y : ℂ → Ω → ℂ := fun z => {ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z with hYdef
  have hYm : ∀ z, Measurable (Y z) := hfwd
  have hY : ∀ z ω, z ∈ (c ω).dom → Y z ω = (c ω).1 z := fun z ω h =>
    indicator_of_mem (show ω ∈ {ω | z ∈ (c ω).dom} from h) _
  have hdomT : ∀ z, {ω | z ∈ ((c ω).trans (recChart (r ω))).dom} =
      {ω | z ∈ (c ω).dom} ∩ {ω | Y z ω ∈ (recChart (r ω)).dom} := by
    intro z
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, hmem]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [hY z ω h1]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← hY z ω h1]; exact h2⟩
  have hdomTm : ∀ z, MeasurableSet {ω | z ∈ ((c ω).trans (recChart (r ω))).dom} := fun z => by
    rw [hdomT]
    exact (hdom z).inter (hd.measurableSet_mem_dom_of_measurable (hYm z))
  have hYd : ∀ z ω, z ∈ ((c ω).trans (recChart (r ω))).dom → Y z ω ∈ (recChart (r ω)).dom := fun z ω h => by
    have h1 := (hmem ω z).1 h
    rw [hY z ω h1.1]
    exact h1.2
  refine ⟨fun ω => (hconf ω).trans (hd.1 ω), fun ω => ?_, fun ω => ?_, hdomTm, fun z => ?_, fun z ε => ?_,
    fun z => ?_⟩
  · -- the lift is continuous
    exact ((hd.2.1 ω).comp ((hconf ω).differentiableOn_fwd.continuousOn.mono (hsub ω)) (hmaps ω)).add
      ((hlc ω).mono (hsub ω))
  · -- the lift is harmonic
    have h1 := LQGMetric.harmonicOnNhd_comp_holo (recChart (r ω)).dom.isOpen
      ((c ω).trans (recChart (r ω))).dom.isOpen (hd.2.2.1 ω)
      ((hconf ω).differentiableOn_fwd.mono (hsub ω)) (hmaps ω)
    exact h1.add ((hharm ω).mono (hsub ω))
  · -- the masked forward map
    have e : ({ω | z ∈ ((c ω).trans (recChart (r ω))).dom}.indicator fun ω => ((c ω).trans (recChart (r ω))).1 z) =
        {ω | z ∈ ((c ω).trans (recChart (r ω))).dom}.indicator
          ({ω | Y z ω ∈ (recChart (r ω)).dom}.indicator fun ω => (recChart (r ω)).1 (Y z ω)) := by
      funext ω
      by_cases hω : z ∈ ((c ω).trans (recChart (r ω))).dom
      · rw [indicator_of_mem (show ω ∈ {ω | z ∈ ((c ω).trans (recChart (r ω))).dom} from hω),
          indicator_of_mem (show ω ∈ {ω | z ∈ ((c ω).trans (recChart (r ω))).dom} from hω),
          indicator_of_mem (show ω ∈ {ω | Y z ω ∈ (recChart (r ω)).dom} from hYd z ω hω), hY z ω ((hmem ω z).1 hω).1]
        rfl
      · rw [indicator_of_notMem (show ω ∉ {ω | z ∈ ((c ω).trans (recChart (r ω))).dom} from hω),
          indicator_of_notMem (show ω ∉ {ω | z ∈ ((c ω).trans (recChart (r ω))).dom} from hω)]
    rw [e]
    exact (hd.measurable_fwd_of_measurable (hYm z)).indicator (hdomTm z)
  · -- closed discs
    rcases lt_or_ge ε 0 with hε | hε
    · have : closedBall z ε = ∅ := closedBall_eq_empty.2 hε
      simp only [this, empty_subset, ofPred_true, MeasurableSet.univ]
    rcases hε.eq_or_lt with rfl | hε
    · simp only [closedBall_zero, singleton_subset_iff]
      exact hdomTm z
    set T : Ω → ℝ := fun ω => (LocalExt.histTime (recHist (r ω)) : ℝ) with hT
    have hTm : Measurable T :=
      measurable_coe_nnreal_real.comp ((LocalExt.measurable_histTime.comp measurable_recHist).comp hr)
    set ι := {q : ℚ × ℚ // Sec7.Coding.ratPt q ∈ closedBall z ε}
    have e : {ω | closedBall z ε ⊆ ((c ω).trans (recChart (r ω))).dom} =
        {ω | closedBall z ε ⊆ (c ω).dom} ∩ {ω | ∃ k : ℕ, ∀ i : ι, ∀ s : ℚ, 0 ≤ (s : ℝ) → (s : ℝ) ≤ T ω →
          2 * (1 / ((k : ℝ) + 1)) ≤
            (tamedZ (Ito.rpath (fun t => recV t (r ω))) (1 / ((k : ℝ) + 1)) (Y (Sec7.Coding.ratPt i.1) ω) s).im} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff]
      constructor
      · intro hB
        have hBc : closedBall z ε ⊆ (c ω).dom := hB.trans (hsub ω)
        refine ⟨hBc, ?_⟩
        have hcont : ContinuousOn (c ω).1 (closedBall z ε) :=
          (hconf ω).differentiableOn_fwd.continuousOn.mono hBc
        have hiff := disjoint_fwdHull_iff_of_dense (continuous_rpath_recV (r ω))
          (LocalExt.histTime (recHist (r ω))).coe_nonneg
          ((isCompact_closedBall z ε).image_of_continuousOn hcont)
          (fun w ⟨x, hx, hxw⟩ => hxw ▸ (hconf ω).fwd_mem (hBc hx))
          (fun i : ι => Y (Sec7.Coding.ratPt i.1) ω)
          (fun i => by rw [hY _ ω (hBc i.2)]; exact mem_image_of_mem _ i.2)
          (fun w ⟨x, hx, hxw⟩ δ hδ => by
            obtain ⟨δ', hδ', hδb⟩ := Metric.continuousAt_iff.1
              (((hconf ω).differentiableOn_fwd.continuousOn x (hBc hx)).continuousAt
                ((c ω).dom.isOpen.mem_nhds (hBc hx))) δ hδ
            obtain ⟨y, hy, hxy⟩ := Sec7.Coding.exists_ratPt_mem_closedBall hε hx hδ'
            refine ⟨⟨y, hy⟩, ?_⟩
            rw [hY _ ω (hBc hy), ← hxw, dist_comm]
            exact hδb (by rw [dist_comm]; exact hxy))
        refine hiff.1 (Set.disjoint_left.2 ?_)
        rintro _ ⟨x, hx, rfl⟩ hK
        exact ((mem_dom_recChart_iff (r ω)).1 ((hmem ω x).1 (hB hx)).2).2 hK
      · rintro ⟨hBc, hk⟩ x hx
        have hcont : ContinuousOn (c ω).1 (closedBall z ε) :=
          (hconf ω).differentiableOn_fwd.continuousOn.mono hBc
        have hiff := disjoint_fwdHull_iff_of_dense (continuous_rpath_recV (r ω))
          (LocalExt.histTime (recHist (r ω))).coe_nonneg
          ((isCompact_closedBall z ε).image_of_continuousOn hcont)
          (fun w ⟨x, hx, hxw⟩ => hxw ▸ (hconf ω).fwd_mem (hBc hx))
          (fun i : ι => Y (Sec7.Coding.ratPt i.1) ω)
          (fun i => by rw [hY _ ω (hBc i.2)]; exact mem_image_of_mem _ i.2)
          (fun w ⟨x, hx, hxw⟩ δ hδ => by
            obtain ⟨δ', hδ', hδb⟩ := Metric.continuousAt_iff.1
              (((hconf ω).differentiableOn_fwd.continuousOn x (hBc hx)).continuousAt
                ((c ω).dom.isOpen.mem_nhds (hBc hx))) δ hδ
            obtain ⟨y, hy, hxy⟩ := Sec7.Coding.exists_ratPt_mem_closedBall hε hx hδ'
            refine ⟨⟨y, hy⟩, ?_⟩
            rw [hY _ ω (hBc hy), ← hxw, dist_comm]
            exact hδb (by rw [dist_comm]; exact hxy))
        have hdisj := hiff.2 hk
        refine (hmem ω x).2 ⟨hBc hx, (mem_dom_recChart_iff (r ω)).2 ⟨(hconf ω).fwd_mem (hBc hx), fun hK => ?_⟩⟩
        exact Set.disjoint_left.1 hdisj (mem_image_of_mem _ hx) hK
    rw [e]
    refine (hcb z ε).inter (measurableSet_setOfPred.2 (Measurable.exists fun k => Measurable.forall fun i =>
      Measurable.forall fun s => ?_))
    by_cases hs : 0 ≤ (s : ℝ)
    · have hm := measurable_tamedZ_recV hr (hYm (Sec7.Coding.ratPt i.1))
        (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity) hs
      refine Measurable.imp measurable_const (Measurable.imp ?_ ?_)
      · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const hTm)
      · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (Complex.measurable_im.comp hm))
    · have e2 : (fun ω => 0 ≤ (s : ℝ) → (s : ℝ) ≤ T ω → 2 * (1 / ((k : ℝ) + 1)) ≤
          (tamedZ (Ito.rpath (fun t => recV t (r ω))) (1 / ((k : ℝ) + 1)) (Y (Sec7.Coding.ratPt i.1) ω) s).im) =
          fun _ => True := by
        funext ω
        simp only [hs, false_implies]
      rw [e2]
      exact measurable_const
  · -- the masked lift
    have e : ({ω | z ∈ ((c ω).trans (recChart (r ω))).dom}.indicator fun ω => ((c ω).trans (recChart (r ω))).2.2 z) =
        {ω | z ∈ ((c ω).trans (recChart (r ω))).dom}.indicator
          (({ω | Y z ω ∈ (recChart (r ω)).dom}.indicator fun ω => (recChart (r ω)).2.2 (Y z ω)) +
            {ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z) := by
      funext ω
      by_cases hω : z ∈ ((c ω).trans (recChart (r ω))).dom
      · rw [indicator_of_mem (show ω ∈ {ω | z ∈ ((c ω).trans (recChart (r ω))).dom} from hω),
          indicator_of_mem (show ω ∈ {ω | z ∈ ((c ω).trans (recChart (r ω))).dom} from hω), Pi.add_apply,
          indicator_of_mem (show ω ∈ {ω | Y z ω ∈ (recChart (r ω)).dom} from hYd z ω hω),
          indicator_of_mem (show ω ∈ {ω | z ∈ (c ω).dom} from ((hmem ω z).1 hω).1), hY z ω ((hmem ω z).1 hω).1]
        rfl
      · rw [indicator_of_notMem (show ω ∉ {ω | z ∈ ((c ω).trans (recChart (r ω))).dom} from hω),
          indicator_of_notMem (show ω ∉ {ω | z ∈ ((c ω).trans (recChart (r ω))).dom} from hω)]
    rw [e]
    exact ((hd.measurable_lift_of_measurable (hYm z)).add (hlift z)).indicator (hdomTm z)

end Trans

end InteractingSLE.Theorem14.WalkInf
