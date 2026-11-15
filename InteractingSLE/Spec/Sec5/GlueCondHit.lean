/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondPath
import InteractingSLE.Spec.Sec5.GlueCondUnionHull
import InteractingSLE.Spec.Sec5.CfAvoidLeftQHit
import InteractingSLE.Spec.Sec5.CfLineRegQ
import InteractingSLE.WangWu.ReverseContactBdryChart

/-!
# The counterflow's boundary non-hitting and transience on the glued space (items G3 (i) and G5 of PROVE-GLUECOND)

Packet PROVE-GLUECOND3. Specification §4.2, proofs of Lemma 4.7 and Proposition 4.9
(`source/spec/p097-144.md#lem-4.7-proof`, `#prop-4.9-proof`, pp. 117–120) and Remark 4.8 (b): the counterflow line
`η′ = R ∘ β` of `h − π/2 χ` in the chart `Q` touches the lower boundary only at its end. In the chart `R` this says that
the generating trace `β` of the counterflow driver is never real at a nonzero point, and tends to `∞`.

**The counterflow word has seed marks** (`exists_seed_admissible_of_isCenteredCounterflowDriver`): the flow-line word of
the counterflow data at `16/κ` (PROVE-SEC5-Q's `CfRegQ.exists_admissible_of_isCenteredCounterflowDriver`) starts with
the seed marks `0⁻`, `0⁺` (index `0` of `flowLineXL`/`flowLineXR`), with admissible partial sums. So PROVE-SEC5-R's
`CfAvoidLeftQ.ae_trace_ne_pos`/`_neg` (Aux. lemmas 24 and 6) keep the trace off `ℝ ∖ {0}`
(`ae_trace_ne_real_of_isCenteredCounterflowDriver`). (No return to `0` is needed below: a filled hull reaches `ℝ` only
at `0` as soon as its trace avoids `ℝ ∖ {0}`.)

**Hulls** (`ofReal_notMem_closure_fwdHull_of_ne`, `isClosed_image_negInv_fwdHull_of_ne`): PROVE-GLUECOND2's
`GlueCondUnionHull` results with the weaker hypothesis "the trace avoids `ℝ ∖ {0}`".

**The glued space.** A Borel certificate of the history (`RealAvoidCert`: rational lower bounds of the distance of the
trace to `{x ∈ ℝ : |x| ≥ 1/(n+1)}` on `[1/(n+1), N]`) carries the non-hitting to the glued space of
`Prop411Q.CfGlueAE` (`cfGlueAE_mem_goodHitSet`). On a good history the hull read from the history is the driver's
hull (`hullAt_eq_fwdHull_of_mem_goodCfSet`), so `R(K′_s) = cfHullQ s y` is closed in `ℂ` and `closure K′_s ∩ ℝ = {0}`
(`isClosed_negInv_fwdHull_of_mem_goodHitSet`, `eq_zero_of_mem_closure_fwdHull_of_mem_goodHitSet`): the hypotheses of
`WangWu.exists_imageTrace` and of Proposition 4.9's boundary correspondence.

**Transience (G5)** from Zhan's Part A inputs at `16/κ` (`Sec5.PartAInputsSixteenDiv`, kept a named input):
`cfGlueAE_mem_goodTransSet`; and Lemma 4.5 at `κ′ = 16/κ` for every admissible seed word (`ae_lemma45_sixteen_div`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.GlueCond

open WangWu hiding ratPt exists_ratPt_dist_lt continuousAt_negInv
open LawUnique Cond44Ref Prop411Q CfRegQ
open Sec4 (regPath regHull histStop)

/-! ### The counterflow word has seed marks -/

section Word

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The centred counterflow of `h − π/2 χ` drives an admissible word at `16/κ` with seed marks `0⁻`, `0⁺`**
(Remark 4.8 (b)): PROVE-SEC5-Q's `CfRegQ.exists_admissible_of_isCenteredCounterflowDriver`, recording that the
flow-line word of the counterflow data has a mark at `0` on each side (its index `0`). -/
theorem exists_seed_admissible_of_isCenteredCounterflowDriver [IsProbabilityMeasure P₂] (hκ : 0 < κ)
    (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂) :
    ∃ (mL mR : ℕ) (yL : Fin mL → ℝ) (yR : Fin mR → ℝ) (σL : Fin mL → ℝ) (σR : Fin mR → ℝ)
      (𝓕₂ : Filtration ℝ≥0 _mΩ₂) (VL₂ : Fin mL → ℝ≥0 → Ω₂ → ℝ) (VR₂ : Fin mR → ℝ≥0 → Ω₂ → ℝ)
      (B₂ : ℝ≥0 → Ω₂ → ℝ), IsOrderedForceWord yL yR ∧ Sec4.HasAdmissiblePartialSums (16 / κ) σL σR yL yR ∧
        IsIntegratedSLEEvolution (16 / κ) yL yR σL σR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
          (∃ i, yL i = 0) ∧ ∃ i, yR i = 0 := by
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
  exact ⟨_, _, _, _, _, _, 𝓕₂, VL₂, VR₂, B₂, Theorem15.isOrderedForceWord_flowLine _ _ 0, hadm, hC'.1,
    ⟨_, Sec4.flowLineXL_zero _ _⟩, ⟨_, Sec4.flowLineXR_zero _ _⟩⟩

/-- **The counterflow's trace never visits `ℝ ∖ {0}`** (chart `R`; Aux. lemmas 24 and 6 at `κ′ = 16/κ`): almost surely
every continuous generating trace of the counterflow driver on `[0, ∞)` avoids every real point `x ≠ 0`. -/
theorem ae_trace_ne_real_of_isCenteredCounterflowDriver [IsProbabilityMeasure P₂] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂) :
    ∀ᵐ ω ∂P₂, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₂ t ω) ⊤ γ → ∀ t : ℝ≥0, ∀ x : ℝ, x ≠ 0 →
      γ t ≠ x := by
  obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE, ⟨iL, hiL⟩, ⟨iR, hiR⟩⟩ :=
    exists_seed_admissible_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw
  have hk' : 0 < 16 / κ := by positivity
  filter_upwards [CfAvoidLeftQ.ae_trace_ne_pos hk' hF' hadm hE, CfAvoidLeftQ.ae_trace_ne_neg hk' hF' hadm hE]
    with ω hR hL γ hγ t x hx
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · exact hL γ hγ t iL x hneg (by rw [hiL]; exact hneg.le)
  · exact hR γ hγ t iR x hpos (by rw [hiR]; exact hpos.le)

end Word

/-! ### Hulls of traces that avoid `ℝ ∖ {0}` -/

section Hull

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The filled hull of a trace that avoids `ℝ ∖ {0}` reaches `ℝ` only at `0`** (GLUECOND2's
`ofReal_notMem_closure_fwdHull` without excluding returns to `0`). -/
theorem ofReal_notMem_closure_fwdHull_of_ne (hw : Continuous fun s : ℝ => w s.toNNReal)
    (hη : IsGeneratingTrace w T η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T)
    (hR : ∀ r : ℝ≥0, 0 < r → r ≤ t → ∀ x : ℝ, x ≠ 0 → η r ≠ x) {y : ℝ} (hy0 : y ≠ 0) :
    (y : ℂ) ∉ closure (fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  have hcont : ContinuousOn η (Icc 0 t) :=
    hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans ht.le
  refine ofReal_notMem_closure_of_isFilling (hη.2.2 t ht) (fun _ hz => hz.1)
    (InteractingSLE.isBounded_fwdHull hw t) (isCompact_Icc.image_of_continuousOn hcont).isClosed ?_ hy0
  rintro x hx ⟨r, hr, hrx⟩
  by_cases h0 : r = 0
  · rw [h0, hη.1] at hrx
    exact hx (by exact_mod_cast hrx.symm)
  · exact hR r (pos_iff_ne_zero.2 h0) hr.2 x hx hrx

/-- A real point of the closure of such a hull is `0`. -/
theorem eq_zero_of_mem_closure_fwdHull_of_ne (hw : Continuous fun s : ℝ => w s.toNNReal)
    (hη : IsGeneratingTrace w T η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T)
    (hR : ∀ r : ℝ≥0, 0 < r → r ≤ t → ∀ x : ℝ, x ≠ 0 → η r ≠ x) {z : ℂ}
    (hz : z ∈ closure (fwdHull (fun s : ℝ => w s.toNNReal) t)) (him : z.im = 0) : z = 0 := by
  have hre : ((z.re : ℝ) : ℂ) = z := Complex.ext rfl (by rw [Complex.ofReal_im, him])
  by_contra hz0
  have hne : z.re ≠ 0 := fun h0 => hz0 (by rw [← hre, h0, Complex.ofReal_zero])
  exact ofReal_notMem_closure_fwdHull_of_ne hw hη ht hR hne (hre ▸ hz)

/-- **`R(K_t)` is closed in `ℂ`** for the filled hull of a trace that avoids `ℝ ∖ {0}`. -/
theorem isClosed_image_negInv_fwdHull_of_ne (hw : Continuous fun s : ℝ => w s.toNNReal)
    (hη : IsGeneratingTrace w T η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T)
    (hR : ∀ r : ℝ≥0, 0 < r → r ≤ t → ∀ x : ℝ, x ≠ 0 → η r ≠ x) :
    IsClosed (negInv '' fwdHull (fun s : ℝ => w s.toNNReal) t) :=
  isClosed_image_negInv_of_closure (fun _ hz => hz.1) (InteractingSLE.isBounded_fwdHull hw t)
    (Aux50Hit.closure_fwdHull_inter_H hw t.coe_nonneg).le fun _ hy =>
      ofReal_notMem_closure_fwdHull_of_ne hw hη ht hR hy

end Hull

/-! ### The driver and hull read from a good history -/

section Bridge

variable {nL nR : ℕ}

/-- On a certified history the driver read from it interpolates the dyadic samples. -/
theorem hDrv_dyadicTime_of_dyCert {y : HistorySpace nL nR} (hy : DyCert y) (p : ℕ × ℕ) :
    hDrv y (dyadicTime p) = dyVal y p := by
  refine tendsto_nhds_unique (hy.tendsto (dyadicTime p)) ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := exists_nat_gt (dyadicTime p)
  obtain ⟨k, hk⟩ := hy.2 N m
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.1 (tendsto_dyadicTime_lowerDyadic (dyadicTime p))
    (1 / ((k : ℝ) + 1)) (by positivity)
  refine ⟨n₀, fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hk _ _ ((dyadicTime_lowerDyadic_le _ n).trans hN.le) hN.le (hn₀ n hn)) hm

/-- **The generating trace read from a good history** (on `[0, ∞)`). -/
theorem isGeneratingTrace_of_mem_goodCfSet {y : HistorySpace nL nR} (hy : y ∈ goodCfSet) :
    IsGeneratingTrace (hDrv y) ⊤ (fun s => LP.traceAt s (hDrv y)) := by
  obtain ⟨⟨_, hc⟩, htr⟩ := hy
  have hw := hc.continuous
  have hw0 := hc.zero
  refine isGeneratingTrace_top_traceAt hw hw0 fun N => ?_
  obtain ⟨η, hη, -⟩ := (Sec7.RandRestart.mem_traceSet_iff hw.continuousOn hw0 fun _ _ =>
    ⟨_, (hw.tendsto _).mono_left nhdsWithin_le_nhds⟩).1 (htr N)
  exact ⟨η, hη⟩

/-- **The regularized driver of a good history stopped at `t` is the history's driver stopped at `t`.** -/
theorem regPath_cfStop_of_mem_goodCfSet {y : HistorySpace 0 0} (hy : y ∈ goodCfSet) (t : ℝ≥0) :
    regPath (cfStop t y) = fun s => hDrv y (min s t) := by
  have hd : DyCert y := hy.1.2
  have h1 : (cfStop t y).1.toNNReal = t := by
    simp [cfStop, Sec4.stopHistory_fst, Aux50Hit.cstop]
  have hcont : Sec4.IsContHist (cfStop t y) := by
    refine ⟨by simp [cfStop, Sec4.stopHistory_fst], fun s => (hDrv y (min s t), Fin.elim0, Fin.elim0),
      (hd.continuous.comp (continuous_id.min continuous_const)).prodMk continuous_const, fun p hp => ?_⟩
    rw [h1] at hp
    rw [Sec4.stopHistory_snd_of_le (s := Aux50Hit.cstop t) (show dyadicTime p ≤ Aux50Hit.cstop t y from hp)]
    refine Prod.ext ?_ (Prod.ext (funext fun i => i.elim0) (funext fun i => i.elim0))
    show dyVal y p = hDrv y (min (dyadicTime p) t)
    rw [min_eq_left hp, hDrv_dyadicTime_of_dyCert hd]
  rw [hcont.regPath_eq]
  funext s
  show (limUnder atTop fun n => ((cfStop t y).2 (lowerDyadic (min s (cfStop t y).1.toNNReal) n)).1) = _
  rw [h1, hDrv_apply]
  congr 1
  funext n
  rw [Sec4.stopHistory_snd_of_le (s := Aux50Hit.cstop t)
    (show dyadicTime (lowerDyadic (min s t) n) ≤ Aux50Hit.cstop t y from
      (dyadicTime_lowerDyadic_le _ n).trans (min_le_right _ _))]
  rfl

/-- **On a good history the hull read from the history is the driver's hull.** -/
theorem hullAt_eq_fwdHull_of_mem_goodCfSet {y : HistorySpace 0 0} (hy : y ∈ goodCfSet) (t : ℝ≥0) :
    hullAt t y = fwdHull (cfDrv y) t := by
  have hw : Continuous (cfDrv y) := (reg_of_mem_goodCfSet hy).2.1
  have heq : fwdHull (Ito.rpath (regPath (cfStop t y))) t = fwdHull (cfDrv y) t :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc (Sec4.continuous_rpath_regPath _) hw t.coe_nonneg fun r hr => by
      rw [Ito.rpath, regPath_cfStop_of_mem_goodCfSet hy t, cfDrv_eq_hDrv]
      simp only
      rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
  show regHull (cfStop t y) = _
  unfold regHull
  rw [histStop_cfStop, heq]
  exact Aux50Hit.closure_fwdHull_inter_H hw t.coe_nonneg

/-- On a good history the reflected counterflow hull is `R(K′_t)` for the driver read from the history. -/
theorem cfHullQ_eq_of_mem_goodCfSet {y : HistorySpace 0 0} (hy : y ∈ goodCfSet) (t : ℝ≥0) :
    cfHullQ t y = negInv '' fwdHull (cfDrv y) t := by
  rw [cfHullQ, hullAt_eq_fwdHull_of_mem_goodCfSet hy]

end Bridge

/-! ### A Borel certificate of real non-hitting -/

section Cert

variable {nL nR : ℕ}

/-- The real points at distance at least `1/(n+1)` from `0`. -/
def farReal (n : ℕ) : Set ℂ := {z | z.im = 0 ∧ 1 / ((n : ℝ) + 1) ≤ |z.re|}

theorem isClosed_farReal (n : ℕ) : IsClosed (farReal n) :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re.abs)

theorem farReal_nonempty (n : ℕ) : (farReal n).Nonempty :=
  ⟨((1 / ((n : ℝ) + 1) : ℝ) : ℂ), Complex.ofReal_im _, by
    rw [Complex.ofReal_re, abs_of_pos (by positivity)]⟩

/-- **The real-avoidance certificate**: rational lower bounds of the distance from the trace read from the history to
`farReal n` on every time interval `[1/(n+1), N]`. -/
def RealAvoidCert (y : HistorySpace nL nR) : Prop :=
  ∀ n N : ℕ, ∃ k : ℕ, ∀ q : ℚ≥0, 1 / ((n : ℝ≥0) + 1) ≤ (q : ℝ≥0) → (q : ℝ≥0) ≤ N →
    1 / ((k : ℝ) + 1) ≤ infDist (LP.traceAt (q : ℝ≥0) (hDrv y)) (farReal n)

theorem measurable_infDist_traceAt (q : ℚ≥0) (S : Set ℂ) :
    Measurable fun y : HistorySpace nL nR => infDist (LP.traceAt (q : ℝ≥0) (hDrv y)) S :=
  (continuous_infDist_pt S).measurable.comp ((LP.measurable_traceAt (q : ℝ≥0)).comp measurable_hDrv)

theorem measurableSet_realAvoidCert : MeasurableSet {y : HistorySpace nL nR | RealAvoidCert y} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun n => Measurable.forall fun N =>
    Measurable.exists fun k => Measurable.forall fun q => ?_)
  exact Measurable.imp measurable_const (Measurable.imp measurable_const
    (measurableSet_setOfPred.1 (measurableSet_le measurable_const (measurable_infDist_traceAt q _))))

/-- **Good hitting histories**: PROVE-SEC5-Q's good counterflow histories with the real-avoidance certificate. -/
def goodHitSet : Set (HistorySpace nL nR) := goodCfSet ∩ {y | RealAvoidCert y}

theorem measurableSet_goodHitSet : MeasurableSet (goodHitSet (nL := nL) (nR := nR)) :=
  measurableSet_goodCfSet.inter measurableSet_realAvoidCert

/-- A rational lower bound on `[a, b]` bounds a continuous function at every time of `[a, b)`. -/
theorem le_of_rat {φ : ℝ≥0 → ℝ} (hφ : Continuous φ) {t a b : ℝ≥0} {c : ℝ} (hat : a ≤ t) (htb : t < b)
    (h : ∀ q : ℚ≥0, a ≤ (q : ℝ≥0) → (q : ℝ≥0) ≤ b → c ≤ φ q) : c ≤ φ t := by
  have hlim : Tendsto (fun m => φ (Sec7.ratAbove t m)) atTop (𝓝 (φ t)) :=
    (hφ.tendsto t).comp (Sec7.tendsto_ratAbove t)
  refine ge_of_tendsto hlim ?_
  have hb : ∀ᶠ m in atTop, ((Sec7.ratAbove t m : ℚ≥0) : ℝ≥0) < b :=
    (Sec7.tendsto_ratAbove t).eventually (gt_mem_nhds htb)
  filter_upwards [hb] with m hm
  exact h _ (hat.trans (Sec7.le_ratAbove t m)) hm.le

/-- **On a good hitting history the trace avoids `ℝ ∖ {0}` at positive times.** -/
theorem traceAt_ne_real_of_mem_goodHitSet {y : HistorySpace nL nR} (hy : y ∈ goodHitSet) {t : ℝ≥0}
    (ht : 0 < t) {x : ℝ} (hx : x ≠ 0) : LP.traceAt t (hDrv y) ≠ x := by
  intro hvis
  have hφ := CfLineRegQ.continuous_traceAt_of_mem_goodCfSet hy.1
  have hpos : (0 : ℝ) < min (t : ℝ) |x| := lt_min ht (abs_pos.2 hx)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  obtain ⟨N, hN⟩ := exists_nat_gt t
  obtain ⟨k, hk⟩ := hy.2 n N
  have hnt : 1 / ((n : ℝ≥0) + 1) ≤ t := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact (hn.trans_le (min_le_left _ _)).le
  have hle := le_of_rat (φ := fun s => infDist (LP.traceAt s (hDrv y)) (farReal n))
    ((continuous_infDist_pt (farReal n)).comp hφ) hnt hN hk
  have hmem : (x : ℂ) ∈ farReal n :=
    ⟨Complex.ofReal_im x, by rw [Complex.ofReal_re]; exact (hn.trans_le (min_le_right _ _)).le⟩
  rw [hvis, infDist_zero_of_mem hmem] at hle
  have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  linarith

/-- The curve read from a good hitting history avoids `ℝ ∖ {0}` at positive times. -/
theorem histLine_ne_real_of_mem_goodHitSet {y : HistorySpace nL nR} (hy : y ∈ goodHitSet) {u : ℝ} (hu : 0 < u)
    {x : ℝ} (hx : x ≠ 0) : histLine y u ≠ x := by
  rw [histLine_eq_traceAt]
  exact traceAt_ne_real_of_mem_goodHitSet hy (Real.toNNReal_pos.2 hu) hx

/-- The driver read from the history of a continuous driver with infinite lifetime is the driver. -/
theorem hDrv_cfHistory {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ ω = ⊤)
    (hw : Continuous fun t => W t ω) : hDrv (cfHistory W ζ ω) = fun t => W t ω := by
  have hval : ∀ p : ℕ × ℕ, dyVal (cfHistory W ζ ω) p = W (dyadicTime p) ω := fun p => by
    simp [dyVal, cfHistory, killedHistory, hζ]
  funext t
  rw [hDrv_apply]
  simp only [hval]
  exact (tendsto_lowerDyadic_of_continuousOn (T := ⊤) hw.continuousOn ENNReal.coe_lt_top).limUnder_eq

/-- The trace read from the history of a continuous driver with a generating trace on `[0, ∞)` is that trace. -/
theorem traceAt_hDrv_cfHistory {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ ω = ⊤)
    (hw : Continuous fun t => W t ω) (hw0 : W 0 ω = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun t => W t ω) ⊤ η) (t : ℝ≥0) : LP.traceAt t (hDrv (cfHistory W ζ ω)) = η t := by
  rw [hDrv_cfHistory hζ hw, LP.traceAt_eq_of_isGeneratingTrace hη hw.continuousOn hw0 ENNReal.coe_lt_top]

/-- **The history of a continuous driver whose generating trace avoids `ℝ ∖ {0}` is a good hitting history.** -/
theorem cfHistory_mem_goodHitSet {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ ω = ⊤)
    (hw : Continuous fun t => W t ω) (hw0 : W 0 ω = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun t => W t ω) ⊤ η) (hne : ∀ t : ℝ≥0, 0 < t → ∀ x : ℝ, x ≠ 0 → η t ≠ x) :
    cfHistory W ζ ω ∈ goodHitSet := by
  have hg := cfHistory_mem_goodCfSet hζ hw hw0 hη
  have htrq : ∀ q : ℚ≥0, LP.traceAt (q : ℝ≥0) (hDrv (cfHistory W ζ ω)) = η q := fun q =>
    traceAt_hDrv_cfHistory hζ hw hw0 hη q
  have hηc : Continuous η :=
    continuousOn_univ.1 (hη.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
  refine ⟨hg, fun n N => ?_⟩
  by_cases hne' : (Icc (1 / ((n : ℝ≥0) + 1)) (N : ℝ≥0)).Nonempty
  · obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn hne'
      ((continuous_infDist_pt (s := farReal n)).comp hηc).continuousOn
    have hnot : η s ∉ farReal n := by
      rintro ⟨him, hre⟩
      have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs.1
      have hre0 : (η s).re ≠ 0 := fun h0 => by
        rw [h0, abs_zero] at hre
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      exact hne s hspos _ hre0 (Complex.ext rfl (by rw [Complex.ofReal_im, him]))
    have hpos := ((isClosed_farReal n).notMem_iff_infDist_pos (farReal_nonempty n)).1 hnot
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    refine ⟨k, fun q hq1 hq2 => ?_⟩
    rw [htrq]
    exact hk.le.trans (isMinOn_iff.1 hmin _ ⟨hq1, hq2⟩)
  · exact ⟨0, fun q hq1 hq2 => absurd ⟨q, hq1, hq2⟩ hne'⟩

/-- **On a good hitting history, `R(K′_s)` is closed in `ℂ` and `closure K′_s` meets `ℝ` only at `0`** (the
hypothesis of `WangWu.exists_imageTrace` for the chart `Ψ = revChart (cfDrv y) s`, and Proposition 4.9's boundary
correspondence). -/
theorem isClosed_negInv_fwdHull_of_mem_goodHitSet {y : HistorySpace nL nR} (hy : y ∈ goodHitSet) {s : ℝ}
    (hs : 0 ≤ s) : IsClosed (negInv '' fwdHull (cfDrv y) s) ∧
      ∀ z ∈ closure (fwdHull (cfDrv y) s), z.im = 0 → z = 0 := by
  have hgen := isGeneratingTrace_of_mem_goodCfSet hy.1
  have hw : Continuous fun r : ℝ => hDrv y r.toNNReal := by
    rw [← cfDrv_eq_hDrv]
    exact (reg_of_mem_goodCfSet hy.1).2.1
  have hR : ∀ r : ℝ≥0, 0 < r → r ≤ s.toNNReal → ∀ x : ℝ, x ≠ 0 → LP.traceAt r (hDrv y) ≠ x :=
    fun r hr _ x hx => traceAt_ne_real_of_mem_goodHitSet hy hr hx
  have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs
  rw [cfDrv_eq_hDrv, ← hs']
  exact ⟨isClosed_image_negInv_fwdHull_of_ne hw hgen ENNReal.coe_lt_top hR,
    fun z hz him => eq_zero_of_mem_closure_fwdHull_of_ne hw hgen ENNReal.coe_lt_top hR hz him⟩

end Cert

/-! ### The glued space (G3 (i)) -/

/-- **G3 (i): almost surely on the glued space the counterflow history is a good hitting history** (in the setting of
`Prop411Q.CfGlueAE`): infinite lifetime, a continuous driver from `0` with a continuous generating trace on `[0, ∞)`,
which avoids `ℝ ∖ {0}`. Consequently `R(K′_s)` is closed in `ℂ`, `closure K′_s ∩ ℝ ⊆ {0}`
(`isClosed_negInv_fwdHull_of_mem_goodHitSet`) and `cfHullQ s y = R(K′_s)` (`cfHullQ_eq_of_mem_goodCfSet`). -/
theorem cfGlueAE_mem_goodHitSet : CfGlueAE.{u} fun _ y => y ∈ goodHitSet := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hΩ₂ : ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodHitSet := by
    obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
      exists_admissible_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw
    have hk' : 0 < 16 / κ := by positivity
    filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE,
      hE.2.2.2.2, ae_trace_ne_real_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw]
      with ω ⟨hζ, _, η, hη⟩ hp hne
    have hw : Continuous fun t => W₂ t ω := by
      have := hp.2.2.2.1
      rw [hζ] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    exact cfHistory_mem_goodHitSet hζ hw hp.1 hη fun t _ x hx => hne η hη t x hx
  exact ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf) (measurable_cfHistory hX₂) hlaw k hk
    measurableSet_goodHitSet hΩ₂

/-! ### Transience (G5) -/

section Trans

variable {nL nR : ℕ}

/-- **Good transient histories**: good hitting histories with PROVE-SEC5-R's transience certificate. -/
def goodTransSet : Set (HistorySpace nL nR) := goodHitSet ∩ {y | CfLineRegQ.TransCert y}

theorem measurableSet_goodTransSet : MeasurableSet (goodTransSet (nL := nL) (nR := nR)) :=
  measurableSet_goodHitSet.inter CfLineRegQ.measurableSet_transCert

/-- On a good transient history the curve read from the history tends to `∞`. -/
theorem tendsto_histLine_of_mem_goodTransSet {y : HistorySpace nL nR} (hy : y ∈ goodTransSet) :
    Tendsto (fun u => ‖histLine y u‖) atTop atTop := by
  have hφ := CfLineRegQ.continuous_traceAt_of_mem_goodCfSet hy.1.1
  refine tendsto_atTop.2 fun M => ?_
  obtain ⟨N, hN⟩ := hy.2 ⌈M⌉₊
  refine eventually_atTop.2 ⟨N, fun u hu => ?_⟩
  have hNu : (N : ℝ≥0) ≤ u.toNNReal := by
    rw [← Real.toNNReal_coe (r := (N : ℝ≥0))]
    exact Real.toNNReal_le_toNNReal (by exact_mod_cast hu)
  have hle := CfLineRegQ.le_norm_of_rat hφ hNu (lt_add_one u.toNNReal) fun q hq _ => hN q hq
  rw [histLine_eq_traceAt]
  exact (Nat.le_ceil M).trans hle

/-- **The history of a continuous driver with a transient generating trace avoiding `ℝ ∖ {0}` is a good transient
history.** -/
theorem cfHistory_mem_goodTransSet {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ ω = ⊤)
    (hw : Continuous fun t => W t ω) (hw0 : W 0 ω = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun t => W t ω) ⊤ η) (hne : ∀ t : ℝ≥0, 0 < t → ∀ x : ℝ, x ≠ 0 → η t ≠ x)
    (htr : Tendsto (fun t => ‖η t‖) atTop atTop) : cfHistory W ζ ω ∈ goodTransSet := by
  refine ⟨cfHistory_mem_goodHitSet hζ hw hw0 hη hne, fun M => ?_⟩
  obtain ⟨T, hT⟩ := eventually_atTop.1 (htr.eventually_ge_atTop (M : ℝ))
  obtain ⟨N, hN⟩ := exists_nat_ge T
  exact ⟨N, fun q hq => by
    rw [CfLineRegQ.trNorm, traceAt_hDrv_cfHistory hζ hw hw0 hη]
    exact hT _ (hN.trans hq)⟩

end Trans

/-- **G5 on the glued space: the counterflow is transient** (Aux. lemma 7 at `κ′ = 16/κ`, from Zhan's Part A inputs at
`16/κ`, the named input `Sec5.PartAInputsSixteenDiv`): almost surely the counterflow history is a good transient
history, so in the chart `Q` the counterflow `η′ = R ∘ β` tends to `0` (`tendsto_histLine_of_mem_goodTransSet`). -/
theorem cfGlueAE_mem_goodTransSet (hA : PartAInputsSixteenDiv) : CfGlueAE.{u} fun _ y => y ∈ goodTransSet := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hΩ₂ : ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodTransSet := by
    obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
      exists_admissible_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw
    have h7 := aux7Statement_sixteen_div_of_partA.{u} hA hκ hκ4 _ _ σL σR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hF' hadm hE
    filter_upwards [h7, hE.2.2.2.2, ae_trace_ne_real_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw]
      with ω ⟨hζ, ⟨η, hη⟩, htr⟩ hp hne
    have hw : Continuous fun t => W₂ t ω := by
      have := hp.2.2.2.1
      rw [hζ] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    exact cfHistory_mem_goodTransSet hζ hw hp.1 hη (fun t _ x hx => hne η hη t x hx) (htr η hη)
  exact ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf) (measurable_cfHistory hX₂) hlaw k hk
    measurableSet_goodTransSet hΩ₂

/-- **Lemma 4.5's boundary behaviour at `κ′ = 16/κ`** (G5, in the chart `R`; for the image counterflow of Lemma 4.7):
for an ordered word at `16/κ` with admissible side partial sums and a mark at `0` on each side, given Zhan's Part A
inputs at `16/κ`, almost surely the lifetime is infinite, there is a continuous generating trace on `[0, ∞)`, and every
such trace avoids `ℝ ∖ {0}` and tends to `∞` (Aux. lemmas 7, 24 and 6). -/
theorem ae_lemma45_sixteen_div (hA : PartAInputsSixteenDiv) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {mL mR : ℕ}
    {yL : Fin mL → ℝ} {yR : Fin mR → ℝ} {σL : Fin mL → ℝ} {σR : Fin mR → ℝ} {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hF : IsOrderedForceWord yL yR) (hadm : Sec4.HasAdmissiblePartialSums (16 / κ) σL σR yL yR)
    (hE : IsIntegratedSLEEvolution (16 / κ) yL yR σL σR P 𝓕 W VL VR B ζ) (hL : ∃ i, yL i = 0)
    (hR : ∃ i, yR i = 0) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
        (∀ t : ℝ≥0, ∀ x : ℝ, x ≠ 0 → η t ≠ x) ∧ Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain ⟨iL, hiL⟩ := hL
  obtain ⟨iR, hiR⟩ := hR
  have hk' : 0 < 16 / κ := by positivity
  filter_upwards [aux7Statement_sixteen_div_of_partA.{u} hA hκ hκ4 yL yR σL σR P 𝓕 W VL VR B ζ hF hadm hE,
    CfAvoidLeftQ.ae_trace_ne_pos hk' hF hadm hE, CfAvoidLeftQ.ae_trace_ne_neg hk' hF hadm hE]
    with ω ⟨hζ, hex, htr⟩ hRp hLn
  refine ⟨hζ, hex, fun η hη => ⟨fun t x hx => ?_, htr η hη⟩⟩
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · exact hLn η hη t iL x hneg (by rw [hiL]; exact hneg.le)
  · exact hRp η hη t iR x hpos (by rw [hiR]; exact hpos.le)

/-- **The image chain of Proposition 4.9's direction exists almost surely** (G3 (i) applied): almost surely on the glued
space, for every counterflow time `s ≥ 0` and flow time `t > 0` such that the flow prefix `η((0, t])` misses
`R(K′_s)`, the flow prefix read in the chart `Ψ = revChart (cfDrv y) s` of `ℍ ∖ R(K′_s)` is, after capacity
parametrization, a simple proper Loewner trace `η′` of a continuous driver `W′` from `0`, with `K^{W′}_T = Ψ(η((0, t]))`
and `η′(T) = Ψ(η(t))` (`WangWu.exists_imageTrace`; its hypothesis that `R(K′_s)` is closed is
`isClosed_negInv_fwdHull_of_mem_goodHitSet`). -/
theorem cfGlueAE_exists_imageTrace : CfGlueAE.{u} fun η y => ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 < t →
    Disjoint (η '' Ioc 0 t) (negInv '' fwdHull (cfDrv y) s) →
    ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ T : ℝ, 0 < T ∧ ∃ η' : ℝ → ℂ, IsLoewnerTrace W' η' ∧
      IsProperArc η' ∧ fwdHull W' T = revChart (cfDrv y) s '' (η '' Ioc 0 t) ∧
        η' T = revChart (cfDrv y) s (η t) := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_glue_fst (μ := P) k hXm (ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1)
  filter_upwards [hline, cfGlueAE_mem_goodHitSet κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂
    hcf hlaw k hk] with p ⟨_, ⟨η, hη, hseq⟩, hprop⟩ hy s hs t ht hdisj
  have hα : IsLoewnerTrace (fun r : ℝ => W r.toNNReal p.1) (seedLine ζ W p.1) := by
    rw [hseq]; exact isLoewnerTrace_of_isGeneratingTrace hη
  have hA := fwdHull_eq_image_Ioc hα hprop ht.le
  obtain ⟨-, hwc, hw0, -⟩ := reg_of_mem_goodCfSet hy.1
  obtain ⟨W', hW'c, hW'0, T, hT, η', h1, h2, h3, h4⟩ := exists_imageTrace hα hprop hwc hw0 hs
    (isClosed_negInv_fwdHull_of_mem_goodHitSet hy hs).1 ht (by rw [hA]; exact hdisj)
  exact ⟨W', hW'c, hW'0, T, hT, η', h1, h2, by rw [h3, hA], h4⟩

end InteractingSLE.Sec5.GlueCond
