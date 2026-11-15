/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtEMain

/-!
# Aux. lemma 53: the continuous driver read from a recorded history

Packet PROVE-LOCEXT-G. The restart of Aux. lemma 53 maps the field by the centred Loewner map `f_T = g_T − W_T` of the
recorded driving history (specification p. 245: "condition on the recorded driving history and map the active field
and future hulls by the centered map `f_τ`"). For the extension's field to be a measurable function of `(h, 𝒳_T)` the
chart must be read from the recorded history `y = 𝒳_T ∈ DrivingHist` (`LocalExtE`'s rational samples) by a measurable
rule. This file reads the driver:

* `IsDrvGood y`: the driver samples `q ↦ (y.2 q).1` start at `0` and are uniformly continuous on `ℚ≥0`, with rational
  moduli (a countable condition, `measurableSet_isDrvGood`);
* `histDrv y t`: on good histories the value at `t` read from the samples at the dyadic rationals decreasing to `t`
  (`valueAt`), and `0` otherwise; it is **continuous in `t` for every `y`** (`continuous_histDrv`), vanishes at `0`
  (`histDrv_zero`) and is jointly measurable (`measurable_histDrv`);
* `histDrv_stoppedHistory`: for the history of a path continuous before its lifetime, stopped at a finite `T` before
  it, `histDrv 𝒳_T t = W_{t ∧ T}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec7

variable {nL nR : ℕ}

/-! ### Good histories -/

section Good

/-- **A good history**: the driver samples start at `0` and are uniformly continuous on `ℚ≥0` with rational moduli. -/
def IsDrvGood (y : DrivingHist nL nR) : Prop :=
  (y.2 0).1 = 0 ∧ ∀ n : ℕ, ∃ m : ℕ, ∀ p q : ℚ≥0,
    |(((p : ℝ≥0) : ℝ) - ((q : ℝ≥0) : ℝ))| < 1 / ((m : ℝ) + 1) → |(y.2 p).1 - (y.2 q).1| ≤ 1 / ((n : ℝ) + 1)

theorem measurable_drvSample (q : ℚ≥0) : Measurable fun y : DrivingHist nL nR => (y.2 q).1 :=
  measurable_fst.comp ((measurable_pi_apply q).comp measurable_snd)

theorem measurableSet_isDrvGood : MeasurableSet {y : DrivingHist nL nR | IsDrvGood y} := by
  have h0 : MeasurableSet {y : DrivingHist nL nR | (y.2 0).1 = 0} :=
    measurableSet_eq_fun (measurable_drvSample 0) measurable_const
  have h1 : MeasurableSet {y : DrivingHist nL nR | ∀ n : ℕ, ∃ m : ℕ, ∀ p q : ℚ≥0,
      |(((p : ℝ≥0) : ℝ) - ((q : ℝ≥0) : ℝ))| < 1 / ((m : ℝ) + 1) →
        |(y.2 p).1 - (y.2 q).1| ≤ 1 / ((n : ℝ) + 1)} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m => MeasurableSet.iInter fun p =>
      MeasurableSet.iInter fun q => ?_
    refine MeasurableSet.iInter fun _ => ?_
    have h := measurableSet_le (((measurable_drvSample (nL := nL) (nR := nR) p).sub
      (measurable_drvSample q)).abs) (measurable_const (a := 1 / ((n : ℝ) + 1)))
    exact h
  exact h0.inter h1

/-- A path `g` continuous on `[0, T]`, with `g 0 = 0` and constant after `T` (`g t = g (min t T)`), gives a good
history. -/
theorem isDrvGood_of_continuousOn {y : DrivingHist nL nR} {g : ℝ≥0 → ℝ} {T : ℝ≥0}
    (hg : ContinuousOn g (Icc 0 T)) (hy : ∀ q : ℚ≥0, (y.2 q).1 = g (min (q : ℝ≥0) T)) (h0 : g 0 = 0) :
    IsDrvGood y := by
  refine ⟨by rw [hy 0]; simpa using h0, fun n => ?_⟩
  have huc : UniformContinuousOn g (Icc 0 T) := isCompact_Icc.uniformContinuousOn_of_continuous hg
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδg⟩ := huc (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m, fun p q hpq => ?_⟩
  rw [hy p, hy q]
  have hmin : dist (min (p : ℝ≥0) T) (min (q : ℝ≥0) T) < δ := by
    have h1 : dist (min (p : ℝ≥0) T) (min (q : ℝ≥0) T) ≤ dist (p : ℝ≥0) (q : ℝ≥0) := by
      rw [NNReal.dist_eq, NNReal.dist_eq]
      push_cast
      exact abs_min_sub_min_le_max _ _ _ _ |>.trans (by simp)
    refine lt_of_le_of_lt h1 ?_
    rw [NNReal.dist_eq]
    exact hpq.trans hm
  have := hδg _ ⟨zero_le, min_le_right _ _⟩ _ ⟨zero_le, min_le_right _ _⟩ hmin
  rw [Real.dist_eq] at this
  exact this.le

end Good

/-! ### The driver read from a history -/

section HistDrv

/-- **The driver read from a recorded history**: on a good history the value at `t` read from the samples at the
dyadic rationals decreasing to `t`; `0` otherwise. -/
def histDrv (y : DrivingHist nL nR) (t : ℝ≥0) : ℝ :=
  {y : DrivingHist nL nR | IsDrvGood y}.indicator (fun y => (valueAt y t).1) y

/-- The recorded (finite part of the) stopping time of a history. -/
def histTime (y : DrivingHist nL nR) : ℝ≥0 := y.1.untopD 0

theorem measurable_histTime : Measurable (histTime (nL := nL) (nR := nR)) :=
  (WithTop.measurable_untopD _).comp measurable_fst

theorem measurable_histDrv : Measurable fun p : DrivingHist nL nR × ℝ≥0 => histDrv p.1 p.2 := by
  classical
  have hv : Measurable fun p : DrivingHist nL nR × ℝ≥0 => (valueAt p.1 p.2).1 := measurable_valueAt.fst
  have hs : MeasurableSet (Prod.fst ⁻¹' {y : DrivingHist nL nR | IsDrvGood y} : Set (DrivingHist nL nR × ℝ≥0)) :=
    measurable_fst measurableSet_isDrvGood
  have e : (fun p : DrivingHist nL nR × ℝ≥0 => histDrv p.1 p.2) =
      fun p => if p ∈ (Prod.fst ⁻¹' {y : DrivingHist nL nR | IsDrvGood y} : Set (DrivingHist nL nR × ℝ≥0))
        then (valueAt p.1 p.2).1 else 0 := by
    funext p
    simp only [histDrv, Set.indicator, mem_preimage]
  rw [e]
  exact Measurable.ite hs hv measurable_const

theorem measurable_histDrv_apply (t : ℝ≥0) : Measurable fun y : DrivingHist nL nR => histDrv y t := by
  have h := (measurable_histDrv (nL := nL) (nR := nR)).comp (measurable_id.prodMk (measurable_const (a := t)))
  exact h

theorem histDrv_of_not {y : DrivingHist nL nR} (hy : ¬ IsDrvGood y) (t : ℝ≥0) : histDrv y t = 0 :=
  indicator_of_notMem (show y ∉ {y : DrivingHist nL nR | IsDrvGood y} from hy) _

theorem histDrv_of_good {y : DrivingHist nL nR} (hy : IsDrvGood y) (t : ℝ≥0) : histDrv y t = (valueAt y t).1 :=
  indicator_of_mem (show y ∈ {y : DrivingHist nL nR | IsDrvGood y} from hy) _

/-- On a good history the samples at the dyadic rationals decreasing to `t` form a Cauchy sequence. -/
theorem cauchySeq_drvSample_upDyad {y : DrivingHist nL nR} (hy : IsDrvGood y) (t : ℝ≥0) :
    CauchySeq fun k => (y.2 (upDyad k t)).1 := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨m, hm⟩ := hy.2 n
  have ht := tendsto_upDyad t
  have hev : ∀ᶠ k in atTop, dist (((upDyad k t : ℚ≥0) : ℝ≥0) : ℝ) (t : ℝ) < 1 / ((m : ℝ) + 1) / 2 := by
    have h' : Tendsto (fun k => (((upDyad k t : ℚ≥0) : ℝ≥0) : ℝ)) atTop (𝓝 (t : ℝ)) :=
      (NNReal.continuous_coe.tendsto _).comp ht
    exact (Metric.tendsto_nhds.1 h') _ (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun a ha b hb => ?_⟩
  have hab : |(((upDyad a t : ℚ≥0) : ℝ≥0) : ℝ) - (((upDyad b t : ℚ≥0) : ℝ≥0) : ℝ)| < 1 / ((m : ℝ) + 1) := by
    have h1 := hN a ha
    have h2 := hN b hb
    rw [Real.dist_eq] at h1 h2
    calc |(((upDyad a t : ℚ≥0) : ℝ≥0) : ℝ) - (((upDyad b t : ℚ≥0) : ℝ≥0) : ℝ)|
        ≤ |(((upDyad a t : ℚ≥0) : ℝ≥0) : ℝ) - t| + |(((upDyad b t : ℚ≥0) : ℝ≥0) : ℝ) - t| := by
          rw [← abs_neg ((((upDyad b t : ℚ≥0) : ℝ≥0) : ℝ) - t)]
          refine (abs_sub_le _ (t : ℝ) _).trans_eq ?_
          ring_nf
      _ < 1 / ((m : ℝ) + 1) / 2 + 1 / ((m : ℝ) + 1) / 2 := add_lt_add h1 h2
      _ = 1 / ((m : ℝ) + 1) := by ring
  rw [Real.dist_eq]
  exact (hm _ _ hab).trans_lt hn

theorem tendsto_drvSample_histDrv {y : DrivingHist nL nR} (hy : IsDrvGood y) (t : ℝ≥0) :
    Tendsto (fun k => (y.2 (upDyad k t)).1) atTop (𝓝 (histDrv y t)) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_drvSample_upDyad hy t)
  rw [histDrv_of_good hy, valueAt, hL.limsup_eq]
  exact hL

/-- The modulus of continuity of a good history passes to the driver read from it. -/
theorem abs_histDrv_sub_le {y : DrivingHist nL nR} (hy : IsDrvGood y) {n m : ℕ}
    (hm : ∀ p q : ℚ≥0, |(((p : ℝ≥0) : ℝ) - ((q : ℝ≥0) : ℝ))| < 1 / ((m : ℝ) + 1) →
      |(y.2 p).1 - (y.2 q).1| ≤ 1 / ((n : ℝ) + 1))
    {s t : ℝ≥0} (hst : |((s : ℝ) - (t : ℝ))| < 1 / ((m : ℝ) + 1)) :
    |histDrv y s - histDrv y t| ≤ 1 / ((n : ℝ) + 1) := by
  have hs := tendsto_drvSample_histDrv hy s
  have ht := tendsto_drvSample_histDrv hy t
  have hdiff : Tendsto (fun k => |(y.2 (upDyad k s)).1 - (y.2 (upDyad k t)).1|) atTop
      (𝓝 |histDrv y s - histDrv y t|) := (hs.sub ht).abs
  have hq : Tendsto (fun k => |(((upDyad k s : ℚ≥0) : ℝ≥0) : ℝ) - (((upDyad k t : ℚ≥0) : ℝ≥0) : ℝ)|) atTop
      (𝓝 |((s : ℝ) - (t : ℝ))|) :=
    ((((NNReal.continuous_coe.tendsto _).comp (tendsto_upDyad s)).sub
      ((NNReal.continuous_coe.tendsto _).comp (tendsto_upDyad t)))).abs
  have hev : ∀ᶠ k in atTop, |(((upDyad k s : ℚ≥0) : ℝ≥0) : ℝ) - (((upDyad k t : ℚ≥0) : ℝ≥0) : ℝ)| <
      1 / ((m : ℝ) + 1) := hq.eventually (gt_mem_nhds hst)
  exact le_of_tendsto hdiff (hev.mono fun k hk => hm _ _ hk)

theorem continuous_histDrv (y : DrivingHist nL nR) : Continuous (histDrv y) := by
  by_cases hy : IsDrvGood y
  · refine (Metric.uniformContinuous_iff.2 fun ε hε => ?_).continuous
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨m, hm⟩ := hy.2 n
    refine ⟨1 / ((m : ℝ) + 1), by positivity, fun {s t} hst => ?_⟩
    rw [NNReal.dist_eq] at hst
    rw [Real.dist_eq]
    exact (abs_histDrv_sub_le hy hm hst).trans_lt hn
  · have e : histDrv y = fun _ => 0 := funext fun t => histDrv_of_not hy t
    rw [e]
    exact continuous_const

theorem histDrv_zero (y : DrivingHist nL nR) : histDrv y 0 = 0 := by
  by_cases hy : IsDrvGood y
  · have h := tendsto_drvSample_histDrv hy 0
    have e : (fun k => (y.2 (upDyad k 0)).1) = fun _ => (y.2 0).1 := by
      funext k
      congr 2
      simp [upDyad, upIdx]
    rw [e, hy.1] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · exact histDrv_of_not hy 0

/-- The driver read from a history agrees with a continuous path recorded in it. -/
theorem histDrv_eq_of_continuousOn {y : DrivingHist nL nR} {g : ℝ≥0 → ℝ} {T : ℝ≥0}
    (hg : ContinuousOn g (Icc 0 T)) (hy : ∀ q : ℚ≥0, (y.2 q).1 = g (min (q : ℝ≥0) T)) (h0 : g 0 = 0)
    (t : ℝ≥0) : histDrv y t = g (min t T) := by
  have hgood := isDrvGood_of_continuousOn hg hy h0
  have hgc : Continuous fun s : ℝ≥0 => g (min s T) := by
    have hm : Continuous fun s : ℝ≥0 => min s T := continuous_id.min continuous_const
    exact hg.comp_continuous hm fun s => ⟨zero_le, min_le_right _ _⟩
  have h1 : Tendsto (fun k => (y.2 (upDyad k t)).1) atTop (𝓝 (g (min t T))) := by
    simp only [hy]
    exact (hgc.tendsto t).comp (tendsto_upDyad t)
  exact tendsto_nhds_unique (tendsto_drvSample_histDrv hgood t) h1

end HistDrv

/-! ### The driver of a recorded history of a path -/

section Recorded

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

theorem histTime_stoppedHistory (X : ℝ≥0 → Ω → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) (T : Ω → ℝ≥0) (ω : Ω) :
    histTime (stoppedHistory X (fun ω => (T ω : WithTop ℝ≥0)) ω) = T ω := by
  simp only [histTime, stoppedHistory, WithTop.untopD_coe]

/-- **The driver read from the recorded history `𝒳_T`** is `W_{t ∧ T}`, for a driver continuous before `ζ`, with
`W₀ = 0` and `T < ζ`. -/
theorem histDrv_stoppedHistory {T : Ω → ℝ≥0} {ω : Ω}
    (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    (hT : (T ω : ℝ≥0∞) < ζ ω) (t : ℝ≥0) :
    histDrv (stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) t =
      W (min t (T ω)) ω := by
  have hsub : Icc 0 (T ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hs.2) hT
  refine histDrv_eq_of_continuousOn (hWc.mono hsub) (fun q => ?_) hW0 t
  have hlt : ((min (q : ℝ≥0) (T ω) : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hT
  simp only [stoppedHistory, stopAt_of_eq_coe (τ := fun ω => (T ω : WithTop ℝ≥0)) rfl, completedState, hlt,
    ↓reduceIte, drivingState]

end Recorded

end LocalExt

end InteractingSLE
