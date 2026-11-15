/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop411Q
import InteractingSLE.Spec.Supplement.GW2ConeData
import InteractingSLE.Spec.Sec7.ContinuityProb3Coding
import InteractingSLE.Spec.ZhanGT4.Prefix
import InteractingSLE.Spec.Theorem15Inputs
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Restart.ChartGauss

/-!
# The counterflow's regularity in the chart `Q` (`Prop411Q.CfRegQStatement`)

Packet PROVE-SEC5-Q. Specification §4.2, Remark 4.8 (b) and Lemma 4.5 (`source/spec/p097-144.md#rem-4.8`, pp. 118–121),
with Aux. lemma 7's trace part at `κ′ = 16/κ` (Part B.1 of the follow-up note, `ZhanGT4.Prefix`).

In the setting of `Prop411Q.CfGlueAE` (an optional hull coupling `(h, W, …)` of an ordered (4.4) word, `0 < κ < 4`, a
centred counterflow `(h₂, W₂, ζ₂)` whose field has the law of `h − π/2 χ`, and a regular conditional law `k` of its
killed history given its field), almost surely on the glued space the counterflow history `y = p.2` has infinite
lifetime, a continuous driver `cfDrv y` started at `0`, and `histLine y` is a Loewner trace of it.

**The counterflow word is admissible at `κ′ = 16/κ`** (Remark 4.8 (b)): the field `h₂` is a GFF with the data
`b = b_F − π/2 χ` of the force word shifted by `−π/2 χ` (the law transfer `isGFFWithBoundaryData_of_map_eq`), so the
driver `W₂` is the flow-line driver of the explicit counterflow word of `counterflowData κ b`
(`Theorem14.GW2Cone.isFlowLineDriver_counterflowData`). Under (4.4) the data `b_F` are `≤ −λ + πχ` on `ℝ₋` and `≥ λ` on
`ℝ₊` (`Sec4.forceBoundaryData_bounds_of_cond44`), so the counterflow data are `≤ −λ − π/2 χ = −λ′ + πχ(κ′)` on `ℝ₋` and
`≥ λ + π/2 χ = λ′ − πχ(κ′)` on `ℝ₊` (`λ′ = λ − π/2 χ`, `χ(κ′) = −χ`): Remark 4.1's bounds at `κ′`, i.e. admissible side
partial sums (`Sec4.hasAdmissiblePartialSums_flowLine`). Hence, almost surely, `ζ₂ = ∞` and `W₂` has a continuous
generating trace on `[0, ∞)` (`ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible`).

**Transfer to the glued space** needs a Borel set of histories (`goodCfSet`): infinite lifetime, a countable
uniform-continuity certificate on the dyadic samples (`DyCert`: the dyadic-limit driver read from the history is then
continuous and starts at `0`), and the Borel trace event `Sec7.RandRestart.traceSet` of that driver on every horizon
`[0, N + 1]`. On this set the finite-horizon traces glue into the measurable trace `s ↦ LP.traceAt s w`
(`isGeneratingTrace_top_traceAt`), which is the curve `histLine y`. The counterflow's history lies in the set almost
surely, and the glued history has the law of the counterflow's history (`WangWu.ae_glue_snd`).

No result here uses Theorem 1.2, Theorem 1.3, `Theorem12ParamStatement` or `Theorem13Statement` (R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CfRegQ

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref Prop411Q

/-! ### The dyadic certificate of a continuous driver -/

section Dyadic

variable {nL nR : ℕ}

/-- The driver sample of a history at the dyadic index `p`. -/
def dyVal (y : HistorySpace nL nR) (p : ℕ × ℕ) : ℝ := (y.2 p).1

theorem measurable_dyVal (p : ℕ × ℕ) : Measurable fun y : HistorySpace nL nR => dyVal y p :=
  measurable_fst.comp ((measurable_pi_apply p).comp measurable_snd)

/-- The driver read from a history (the dyadic limits from below), as a path on `ℝ≥0`. -/
def hDrv (y : HistorySpace nL nR) : ℝ≥0 → ℝ := (pathsOfHistory y).2.1

theorem measurable_hDrv : Measurable (hDrv (nL := nL) (nR := nR)) :=
  measurable_fst.comp (measurable_snd.comp measurable_pathsOfHistory)

theorem hDrv_apply (y : HistorySpace nL nR) (t : ℝ≥0) :
    hDrv y t = limUnder atTop fun n => dyVal y (lowerDyadic t n) := rfl

theorem cfDrv_eq_hDrv (y : HistorySpace nL nR) : cfDrv y = fun s : ℝ => hDrv y s.toNNReal := rfl

theorem histLine_eq_traceAt (y : HistorySpace nL nR) :
    histLine y = fun s : ℝ => LP.traceAt s.toNNReal (hDrv y) := rfl

/-- **The dyadic certificate**: the sample at the index `(0, 0)` is `0`, and the dyadic samples are uniformly
continuous in the dyadic time on every `[0, N]` (a countable condition). -/
def DyCert (y : HistorySpace nL nR) : Prop :=
  dyVal y (0, 0) = 0 ∧ ∀ N m : ℕ, ∃ k : ℕ, ∀ p q : ℕ × ℕ, dyadicTime p ≤ N → dyadicTime q ≤ N →
    dist (dyadicTime p) (dyadicTime q) < 1 / ((k : ℝ) + 1) → |dyVal y p - dyVal y q| ≤ 1 / ((m : ℝ) + 1)

theorem measurableSet_dyCert : MeasurableSet {y : HistorySpace nL nR | DyCert y} := by
  refine MeasurableSet.inter (measurableSet_eq_fun (measurable_dyVal _) measurable_const) ?_
  refine measurableSet_setOfPred.2 (Measurable.forall fun N => Measurable.forall fun m => Measurable.exists
    fun k => Measurable.forall fun p => Measurable.forall fun q => ?_)
  refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const ?_))
  exact measurableSet_setOfPred.1
    (measurableSet_le ((measurable_dyVal p).sub (measurable_dyVal q)).abs measurable_const)

variable {y : HistorySpace nL nR}

/-- On a certified history the dyadic samples below `t` are Cauchy. -/
theorem DyCert.cauchySeq (hy : DyCert y) (t : ℝ≥0) :
    CauchySeq fun n => dyVal y (lowerDyadic t n) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
  obtain ⟨k, hk⟩ := hy.2 N m
  obtain ⟨n₁, hn₁⟩ := Metric.cauchySeq_iff.1 (tendsto_dyadicTime_lowerDyadic t).cauchySeq
    (1 / ((k : ℝ) + 1)) (by positivity)
  have hle : ∀ n, dyadicTime (lowerDyadic t n) ≤ N := fun n =>
    (dyadicTime_lowerDyadic_le t n).trans (by exact_mod_cast hN.le)
  refine ⟨n₁, fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hk _ _ (hle n) (hle n₁) (hn₁ n hn n₁ le_rfl)) hm

theorem DyCert.tendsto (hy : DyCert y) (t : ℝ≥0) :
    Tendsto (fun n => dyVal y (lowerDyadic t n)) atTop (𝓝 (hDrv y t)) :=
  (hy.cauchySeq t).tendsto_limUnder

/-- **On a certified history the driver read from it is continuous.** -/
theorem DyCert.continuous (hy : DyCert y) : Continuous (hDrv y) := by
  rw [Metric.continuous_iff]
  intro t ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((t : ℝ) + 1)
  obtain ⟨k, hk⟩ := hy.2 N m
  refine ⟨min 1 (1 / ((k : ℝ) + 1)), lt_min one_pos (by positivity), fun t' ht' => ?_⟩
  have h1 : dist t' t < 1 := lt_of_lt_of_le ht' (min_le_left _ _)
  have h2 : dist t' t < 1 / ((k : ℝ) + 1) := lt_of_lt_of_le ht' (min_le_right _ _)
  have ht'N : (t' : ℝ) ≤ N := by
    rw [NNReal.dist_eq] at h1
    have := (abs_lt.1 h1).2
    linarith
  have htN : (t : ℝ) ≤ N := by linarith
  have hle : ∀ u : ℝ≥0, (u : ℝ) ≤ N → ∀ n, dyadicTime (lowerDyadic u n) ≤ N := fun u hu n =>
    (dyadicTime_lowerDyadic_le u n).trans (by exact_mod_cast hu)
  have hd : ∀ᶠ n in atTop, dist (dyadicTime (lowerDyadic t' n)) (dyadicTime (lowerDyadic t n)) <
      1 / ((k : ℝ) + 1) :=
    ((tendsto_dyadicTime_lowerDyadic t').dist (tendsto_dyadicTime_lowerDyadic t)).eventually (gt_mem_nhds h2)
  have hev : ∀ᶠ n in atTop, |dyVal y (lowerDyadic t' n) - dyVal y (lowerDyadic t n)| ≤ 1 / ((m : ℝ) + 1) := by
    filter_upwards [hd] with n hn
    exact hk _ _ (hle t' ht'N n) (hle t htN n) hn
  have hlim := le_of_tendsto (((hy.tendsto t').sub (hy.tendsto t)).abs) hev
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hlim hm

/-- **On a certified history the driver read from it starts at `0`.** -/
theorem DyCert.zero (hy : DyCert y) : hDrv y 0 = 0 := by
  have hconst : ∀ n, dyVal y (lowerDyadic 0 n) = dyVal y (0, 0) := by
    intro n
    have hl : lowerDyadic 0 n = (n, 0) := by simp [lowerDyadic]
    rw [hl]
    have ht : ∀ p : ℕ × ℕ, p.2 = 0 → dyadicTime p = 0 := fun p hp => by simp [dyadicTime, hp]
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨k, hk⟩ := hy.2 0 m
    have h := hk (n, 0) (0, 0) (by rw [ht _ rfl]; simp) (by rw [ht _ rfl]; simp)
      (by rw [ht (n, 0) rfl, ht (0, 0) rfl, dist_self]; positivity)
    rw [Real.dist_eq]
    exact h.trans hm.le
  have h := hy.tendsto 0
  simp only [hconst] at h
  rw [tendsto_nhds_unique h tendsto_const_nhds, hy.1]

end Dyadic

/-! ### Gluing finite-horizon traces -/

section Glue

/-- **Finite-horizon generating traces glue into the measurable trace.** If a continuous driver `w` with `w 0 = 0`
has a continuous generating trace on every horizon `[0, N + 1]`, then `s ↦ LP.traceAt s w` is a continuous generating
trace on `[0, ∞)`. -/
theorem isGeneratingTrace_top_traceAt {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (h : ∀ N : ℕ, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) η) :
    IsGeneratingTrace w ⊤ (fun s => LP.traceAt s w) := by
  choose η hη using h
  have heq : ∀ N : ℕ, ∀ s : ℝ≥0, s < (N : ℝ≥0) + 1 → LP.traceAt s w = η N s := fun N s hs =>
    LP.traceAt_eq_of_isGeneratingTrace (hη N) hw.continuousOn hw0 (ENNReal.coe_lt_coe.2 hs)
  have hbig : ∀ t : ℝ≥0, ∃ N : ℕ, t < (N : ℝ≥0) + 1 := fun t => by
    obtain ⟨N, hN⟩ := exists_nat_gt t
    exact ⟨N, hN.trans (lt_add_one _)⟩
  refine ⟨?_, ?_, fun t _ => ?_⟩
  · show LP.traceAt 0 w = 0
    rw [heq 0 0 (by simp)]
    exact (hη 0).1
  · refine Continuous.continuousOn (continuous_iff_continuousAt.2 fun t => ?_)
    obtain ⟨N, hN⟩ := hbig t
    have hU : Iio ((N : ℝ≥0) + 1) ∈ 𝓝 t := Iio_mem_nhds hN
    have hc : ContinuousAt (η N) t := by
      refine ((hη N).2.1.mono fun s (hs : s < (N : ℝ≥0) + 1) => ?_).continuousAt
        (mem_of_superset hU fun s hs => hs)
      · show ((s : ℝ≥0∞)) ≤ (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞)
        exact ENNReal.coe_le_coe.2 hs.le
    refine hc.congr ?_
    filter_upwards [hU] with s hs
    exact (heq N s hs).symm
  · obtain ⟨N, hN⟩ := hbig t
    have himg : (fun s => LP.traceAt s w) '' Icc 0 t = η N '' Icc 0 t :=
      image_congr fun s hs => heq N s (lt_of_le_of_lt hs.2 hN)
    rw [himg]
    exact (hη N).2.2 t (ENNReal.coe_lt_coe.2 hN)

end Glue

/-! ### The Borel set of good counterflow histories -/

section Good

variable {nL nR : ℕ}

/-- **Good counterflow histories**: infinite lifetime, the dyadic certificate, and the Borel trace event of the
driver read from the history on every horizon `[0, N + 1]`. -/
def goodCfSet : Set (HistorySpace nL nR) :=
  {y | y.1 = ⊤} ∩ {y | DyCert y} ∩
    {y | ∀ N : ℕ, (hDrv y, (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet}

theorem measurableSet_goodCfSet : MeasurableSet (goodCfSet (nL := nL) (nR := nR)) := by
  refine (MeasurableSet.inter (measurable_fst (measurableSet_singleton ⊤)) measurableSet_dyCert).inter ?_
  have e : {y : HistorySpace nL nR | ∀ N : ℕ,
      (hDrv y, (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet} =
      ⋂ N : ℕ, (fun y : HistorySpace nL nR => (hDrv y, (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞))) ⁻¹'
        Sec7.RandRestart.traceSet := by
    ext y; simp
  rw [e]
  exact MeasurableSet.iInter fun N =>
    (measurable_hDrv.prodMk measurable_const) Sec7.RandRestart.measurableSet_traceSet

/-- **The regularity of a good counterflow history**: infinite lifetime, a continuous driver starting at `0`, and the
curve read from the history is a Loewner trace of it. -/
theorem reg_of_mem_goodCfSet {y : HistorySpace nL nR} (hy : y ∈ goodCfSet) :
    y.1 = ⊤ ∧ Continuous (cfDrv y) ∧ cfDrv y 0 = 0 ∧ IsLoewnerTrace (cfDrv y) (histLine y) := by
  obtain ⟨⟨hζ, hc⟩, htr⟩ := hy
  have hw := hc.continuous
  have hw0 := hc.zero
  have hev : ∀ N : ℕ, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (hDrv y) (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) η := by
    intro N
    have h := (Sec7.RandRestart.mem_traceSet_iff hw.continuousOn hw0 fun _ _ =>
      ⟨_, (hw.tendsto _).mono_left nhdsWithin_le_nhds⟩).1 (htr N)
    obtain ⟨η, hη, -⟩ := h
    exact ⟨η, hη⟩
  have hgen := isGeneratingTrace_top_traceAt hw hw0 hev
  refine ⟨hζ, ?_, ?_, ?_⟩
  · rw [cfDrv_eq_hDrv]
    exact hw.comp continuous_real_toNNReal
  · rw [cfDrv_eq_hDrv]
    simpa using hw0
  · rw [cfDrv_eq_hDrv, histLine_eq_traceAt]
    exact isLoewnerTrace_of_isGeneratingTrace hgen

end Good

/-! ### The counterflow's history is good almost surely -/

section Counterflow

/-- **A field with the law of a GFF with data `g` is a GFF with data `g`.** -/
theorem isGFFWithBoundaryData_of_map_eq {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂] {P : Measure Ω}
    {P₂ : Measure Ω₂} {h : Ω → DistOn upperHalfPlaneOpens} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {g : ℝ → ℝ}
    {S : Set ℝ} (hh : IsGFFWithBoundaryData P h g S) (hh₂ : Measurable h₂) (hlaw : P.map h = P₂.map h₂) :
    IsGFFWithBoundaryData P₂ h₂ g S := by
  refine ⟨hh₂, fun u hu => ?_⟩
  have hXm : ∀ φ : TestOn upperHalfPlaneOpens,
      Measurable fun d : DistOn upperHalfPlaneOpens => d φ - ∫ z, u z * φ z :=
    fun φ => (LQGMetric.measurable_distOn_apply φ).sub_const _
  have h1 := Restart.isZBGFFProcess_map (X := fun φ (d : DistOn upperHalfPlaneOpens) => d φ - ∫ z, u z * φ z)
    hh.1 hXm (hh.2 u hu)
  rw [hlaw] at h1
  exact Restart.isZBGFFProcess_comp hh₂ h1

/-- The field of a centred counterflow is measurable (it is the return field of the measurable parameter field). -/
theorem measurable_of_isCenteredCounterflowDriver {κ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) : Measurable h := by
  obtain ⟨b', J', h', -, htr, h'', 𝓕, VL, VR, B, htac, hC⟩ := hcf
  have e : h'' = h' := funext fun ω =>
    Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htac ω)
  subst e
  have hfun : h = fun ω => Sec7.StripSysField.returnField _ _ (h'' ω) :=
    funext fun ω => Theorem14.GW2Cone.eq_returnField_of_isChartTransport (htr ω)
  rw [hfun]
  exact (Sec7.StripSysField.measurable_returnField _ _).comp hC.2.1

/-- **The counterflow data are Remark 4.1's bounds at `κ′ = 16/κ`** (Remark 4.8 (b)): if `g ≤ −λ + π/2 χ` on `ℝ₋`
and `g ≥ λ − π/2 χ` on `ℝ₊`, the data `counterflowData κ g` are `≤ −λ′ + πχ(κ′)` on `ℝ₋` and `≥ λ′ − πχ(κ′)` on
`ℝ₊` (`λ′ = λ − π/2 χ`, `χ(κ′) = −χ`). -/
theorem counterflowData_bounds {κ : ℝ} (hκ : 0 < κ) {g : ℝ → ℝ}
    (hL : ∀ x : ℝ, x < 0 → g x ≤ -sleLambda κ + π / 2 * chiC κ)
    (hR : ∀ x : ℝ, 0 < x → sleLambda κ - π / 2 * chiC κ ≤ g x) :
    (∀ y : ℝ, y < 0 → Sec7.StripSysField.counterflowData κ g y ≤ -sleLambda (16 / κ) + π * chiC (16 / κ)) ∧
      ∀ y : ℝ, 0 < y → sleLambda (16 / κ) - π * chiC (16 / κ) ≤ Sec7.StripSysField.counterflowData κ g y := by
  have hlam := Sec4.sleLambda_sixteen_div_eq_sub hκ
  have hchi := Sec4.chiC_sixteen_div hκ
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have hpos : 0 < -y⁻¹ := neg_pos.2 (inv_lt_zero.2 hy)
    have h1 := hR _ hpos
    simp only [Sec7.StripSysField.counterflowData, Sec7.StripSysField.inverseData,
      Sec7.StripSysField.returnData, Sec7.StripSysField.cfOffset, Sec7.StripSysField.cfCoeff,
      Sec7.StripSysField.liftBoundary, hy, ↓reduceIte, hchi, hlam]
    nlinarith [Real.pi_pos]
  · have hneg : -y⁻¹ < 0 := neg_neg_iff_pos.2 (inv_pos.2 hy)
    have h1 := hL _ hneg
    simp only [Sec7.StripSysField.counterflowData, Sec7.StripSysField.inverseData,
      Sec7.StripSysField.returnData, Sec7.StripSysField.cfOffset, Sec7.StripSysField.cfCoeff,
      Sec7.StripSysField.liftBoundary, not_lt.2 hy.le, ↓reduceIte, hchi, hlam]
    nlinarith [Real.pi_pos]

/-- **The history of a continuous driver with infinite lifetime and a generating trace is good.** -/
theorem cfHistory_mem_goodCfSet {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ ω = ⊤)
    (hw : Continuous fun t => W t ω) (hw0 : W 0 ω = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun t => W t ω) ⊤ η) : cfHistory W ζ ω ∈ goodCfSet := by
  have hval : ∀ p : ℕ × ℕ, dyVal (cfHistory W ζ ω) p = W (dyadicTime p) ω := fun p => by
    simp [dyVal, cfHistory, killedHistory, hζ]
  have hdrv : hDrv (cfHistory W ζ ω) = fun t => W t ω := by
    funext t
    rw [hDrv_apply]
    simp only [hval]
    exact (tendsto_lowerDyadic_of_continuousOn (T := ⊤) hw.continuousOn ENNReal.coe_lt_top).limUnder_eq
  refine ⟨⟨by simp [cfHistory, killedHistory, hζ], ⟨?_, fun N m => ?_⟩⟩, fun N => ?_⟩
  · rw [hval]; simpa [dyadicTime] using hw0
  · have hu : UniformContinuousOn (fun t => W t ω) (Icc 0 (N : ℝ≥0)) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hw.continuousOn
    obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 hu (1 / ((m : ℝ) + 1)) (by positivity)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    refine ⟨k, fun p q hp hq hpq => ?_⟩
    rw [hval, hval]
    have := hδu _ ⟨zero_le, hp⟩ _ ⟨zero_le, hq⟩ (lt_trans hpq hk)
    rw [Real.dist_eq] at this
    exact this.le
  · rw [hdrv]
    refine (Sec7.RandRestart.mem_traceSet_iff hw.continuousOn hw0 fun _ _ =>
      ⟨_, (hw.tendsto _).mono_left nhdsWithin_le_nhds⟩).2
      ⟨η, ⟨hη.1, hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top,
        fun t _ => hη.2.2 t ENNReal.coe_lt_top⟩, fun h => absurd h ENNReal.coe_ne_top⟩

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The centred counterflow of `h − π/2 χ` is the flow line of an admissible word at `16/κ`** (Remark 4.8 (b)):
for a (4.4) word, `0 < κ < 4`, the driver of a centred counterflow whose field has the law of `h − π/2 χ` drives an
integrated `SLE_{16/κ}(ρ′)` evolution of an ordered force word with admissible side partial sums. -/
theorem exists_admissible_of_isCenteredCounterflowDriver [IsProbabilityMeasure P₂] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂) :
    ∃ (mL mR : ℕ) (yL : Fin mL → ℝ) (yR : Fin mR → ℝ) (σL : Fin mL → ℝ) (σR : Fin mR → ℝ)
      (𝓕₂ : Filtration ℝ≥0 _mΩ₂) (VL₂ : Fin mL → ℝ≥0 → Ω₂ → ℝ) (VR₂ : Fin mR → ℝ≥0 → Ω₂ → ℝ)
      (B₂ : ℝ≥0 → Ω₂ → ℝ), IsOrderedForceWord yL yR ∧ Sec4.HasAdmissiblePartialSums (16 / κ) σL σR yL yR ∧
        IsIntegratedSLEEvolution (16 / κ) yL yR σL σR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ := by
  set c : ℝ := -(π / 2 * chiC κ) with hc
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + c with hbdef
  have hb : IsPiecewiseConstantBoundaryData b (forceJumpFinset xL xR) := isPiecewiseConstant_forceData κ ρL ρR xL xR c
  have hh : IsGFFWithBoundaryData P h (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) := ⟨hC.2.1, hC.2.2.1⟩
  have hh' := isGFFWithBoundaryData_flowField_zero hh c
  rw [← coe_forceJumpFinset] at hh'
  have hh'' : IsGFFWithBoundaryData P (fun ω => cfField κ (h ω)) b (forceJumpFinset xL xR) := hh'
  have hh₂ := isGFFWithBoundaryData_of_map_eq hh'' (measurable_of_isCenteredCounterflowDriver hcf) hlaw
  obtain ⟨h', -, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hh₂ hcf
  obtain ⟨h'', 𝓕₂, VL₂, VR₂, B₂, -, hC'⟩ := hfl
  have hk' : 0 < 16 / κ := by positivity
  obtain ⟨hbL, hbR⟩ := Sec4.forceBoundaryData_bounds_of_cond44 hκ hκ4 hF h44
  have hbd := counterflowData_bounds hκ (g := b) (fun x hx => by
      have := hbL x hx
      simp only [hbdef, hc]
      linarith) (fun x hx => by
      have := hbR x hx.le
      simp only [hbdef, hc]
      linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_flowLine hk' (Sec7.StripSysField.isPiecewiseConstant_counterflowData κ hb)
    (fun x hx _ => hbd.1 x hx) (fun x hx _ => hbd.2 x hx)
  exact ⟨_, _, _, _, _, _, 𝓕₂, VL₂, VR₂, B₂, Theorem15.isOrderedForceWord_flowLine _ _ 0, hadm, hC'.1⟩

/-- **The counterflow's history is good almost surely.** -/
theorem ae_cfHistory_mem_goodCfSet [IsProbabilityMeasure P₂] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂) :
    ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodCfSet := by
  obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
    exists_admissible_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw
  have hk' : 0 < 16 / κ := by positivity
  filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE,
    hE.2.2.2.2] with ω ⟨hζ, _, η, hη⟩ hp
  have hw : Continuous fun t => W₂ t ω := by
    have := hp.2.2.2.1
    rw [hζ] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  exact cfHistory_mem_goodCfSet hζ hw hp.1 hη

end Counterflow

/-! ### The named input `CfRegQStatement` -/

/-- **The counterflow's regularity in the chart `Q`** (`Prop411Q.CfRegQStatement`; Remark 4.8 (b), Lemma 4.5 and
Aux. lemma 7 at `κ′ = 16/κ`): almost surely on the glued space the counterflow history has infinite lifetime, a
continuous driver starting at `0`, and `histLine` is a Loewner trace of it. -/
theorem cfRegQStatement : CfRegQStatement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hg := ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf) (measurable_cfHistory hX₂) hlaw k hk
    measurableSet_goodCfSet (ae_cfHistory_mem_goodCfSet hκ hκ4 hF h44 hC hcf hlaw)
  filter_upwards [hg] with p hp
  exact reg_of_mem_goodCfSet hp

end InteractingSLE.Sec5.CfRegQ
