/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfLineRegQSeed
import InteractingSLE.Spec.Sec5.CfRegQ
import InteractingSLE.Spec.Sec5.Prop51Q
import InteractingSLE.Spec.Sec5.CrossRestartLaw

/-!
# The counterflow line of Proposition 5.5's configuration is regular (`Prop51Q.CfLineRegularQStatement`)

Packet PROVE-SEC5-R. Specification §5, p. 129: "`η′` intersects `∂_L𝒮` only when it terminates at `0`. Consequently,
`η′` is almost surely continuous (recall Remark 2.3)", with Aux. lemma 7 at `κ′ = 16/κ`.

**Setting** (PROVE-SEC5-P's named input `Prop51Q.CfLineRegularQStatement`): `h` is a GFF with the data `−a | b` of
Figure 7.1 (`b ≥ λ − θ₁χ`, `a ≥ λ − πχ + θ₁χ`), and a centred counterflow `(h₂, W₂, ζ₂)` has the field law of
`h + (θ₁ − π/2)χ`; its killed history is glued to `h` through a regular conditional law `k`.

**The counterflow word is a seed word at `16/κ`.** The field `h₂` is a GFF with the data
`g = −a + (θ₁ − π/2)χ | b + (θ₁ − π/2)χ` (law transfer `CfRegQ.isGFFWithBoundaryData_of_map_eq`), so `W₂` drives the
flow line at `16/κ` of the counterflow data of `g` (`Theorem14.GW2Cone.isFlowLineDriver_counterflowData`). These data
jump only at `0` (`counterflowJumps {0} = {0}`), so every mark of the word sits at the seed (`flowLineXL_eq_zero`,
`flowLineXR_eq_zero`), and `g ≤ −λ + π/2 χ` on `ℝ₋`, `g ≥ λ − π/2 χ` on `ℝ₊` make the word admissible at `16/κ`
(`CfRegQ.counterflowData_bounds`, `Sec4.hasAdmissiblePartialSums_flowLine`):
`exists_seed_of_isCenteredCounterflowDriver`.

**Regularity.** Aux. lemma 7 at `16/κ` (from Zhan's Part A inputs at `16/κ`, `Sec5.PartAInputsSixteenDiv`, the named
input already used by `Sec5.Prop411` and `Sec5.Prop55`) gives infinite lifetime, a continuous trace and transience;
`ae_trace_ne_zero_of_seed` (scaling, `CfLineRegQSeed.lean`) gives no return to `0`. A Borel certificate of the history
(`goodRegSet`: PROVE-SEC5-Q's `CfRegQ.goodCfSet` plus rational lower bounds of the trace norm on compact time intervals
away from `0` and at late times) carries the four properties to the glued space (`WangWu.ae_glue_snd`).

## Main results

* `exists_seed_of_isCenteredCounterflowDriver`: the counterflow drives an admissible seed word at `16/κ`.
* `goodRegSet`, `measurableSet_goodRegSet`, `reg_of_mem_goodRegSet`, `cfHistory_mem_goodRegSet`.
* **`cfLineRegularQStatement_of_partA`**: `Prop51Q.CfLineRegularQStatement` from `PartAInputsSixteenDiv`.
* `prop51QStatement_of_partA_of_cfAvoidLeft`: `Cond44Ref.Prop51QStatement` from `PartAInputsSixteenDiv` and
  `Prop51Q.CfAvoidLeftQStatement`.

No result here uses Theorem 1.2, Theorem 1.3, `Theorem12ParamStatement` or `Theorem13Statement` (R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CfLineRegQ

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref Prop411Q CfRegQ

/-! ### The counterflow word of the data `−a | b` is a seed word -/

/-- The left marks of the flow-line word of data whose jump candidates all sit at `0` are the seed `0⁻`. -/
theorem flowLineXL_eq_zero {g : ℝ → ℝ} {J : Finset ℝ} (hJ : ∀ x ∈ J, x = 0) :
    flowLineXL g J 0 = fun _ => 0 := by
  funext i
  unfold flowLineXL
  refine Fin.cases rfl (fun j => ?_) i
  exfalso
  have hmem := Finset.orderEmbOfFin_mem ((PiecewiseConstantBoundaryData.jumpSet g J).filter (· < 0)) rfl j
  rw [Finset.mem_filter] at hmem
  have h0 := hJ _ (Finset.mem_filter.1 hmem.1).1
  linarith [hmem.2]

/-- The right marks of the flow-line word of data whose jump candidates all sit at `0` are the seed `0⁺`. -/
theorem flowLineXR_eq_zero {g : ℝ → ℝ} {J : Finset ℝ} (hJ : ∀ x ∈ J, x = 0) :
    flowLineXR g J 0 = fun _ => 0 := by
  funext i
  unfold flowLineXR
  refine Fin.cases rfl (fun j => ?_) i
  exfalso
  have hmem := Finset.orderEmbOfFin_mem ((PiecewiseConstantBoundaryData.jumpSet g J).filter (0 < ·)) rfl j
  rw [Finset.mem_filter] at hmem
  have h0 := hJ _ (Finset.mem_filter.1 hmem.1).1
  linarith [hmem.2]

section Word

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The counterflow of `h + (θ₁ − π/2)χ` drives an admissible seed word at `16/κ`** (Remark 4.8 (b) in Proposition
5.5's configuration): for the data `−a | b` with `b ≥ λ − θ₁χ` and `a ≥ λ − πχ + θ₁χ`, the driver of a centred
counterflow whose field has the law of `h + (θ₁ − π/2)χ` drives an integrated `SLE_{16/κ}(σ)` evolution whose marks all
sit at the seed, with admissible side partial sums. -/
theorem exists_seed_of_isCenteredCounterflowDriver [IsProbabilityMeasure P₂] (hκ : 0 < κ) {a b θ₁ : ℝ}
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (ha : sleLambda κ - π * chiC κ + θ₁ * chiC κ ≤ a)
    (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ))
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂) :
    ∃ (mL mR : ℕ) (σL : Fin mL → ℝ) (σR : Fin mR → ℝ) (𝓕₂ : Filtration ℝ≥0 _mΩ₂)
      (VL₂ : Fin mL → ℝ≥0 → Ω₂ → ℝ) (VR₂ : Fin mR → ℝ≥0 → Ω₂ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ),
      Sec4.HasAdmissiblePartialSums (16 / κ) σL σR (fun _ => 0) (fun _ => 0) ∧
        IsIntegratedSLEEvolution (16 / κ) (fun _ => 0) (fun _ => 0) σL σR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ := by
  set g : ℝ → ℝ := fun x => (Sec7.prop74Data a b x + θ₁ * chiC κ) + -(π / 2 * chiC κ) with hgdef
  have hh1 := isGFFWithBoundaryData_flowField_zero hh (θ₁ * chiC κ)
  have hh2 := isGFFWithBoundaryData_flowField_zero hh1 (-(π / 2 * chiC κ))
  have hh2' : IsGFFWithBoundaryData P (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) g
      ((({0} : Finset ℝ)) : Set ℝ) := hh2
  have hgpc : IsPiecewiseConstantBoundaryData g {0} := fun y hy => by
    filter_upwards [Sec7.isPiecewiseConstant_prop74Data a b y hy] with z hz
    simp only [hgdef, hz]
  have hh₂ := isGFFWithBoundaryData_of_map_eq hh2' (measurable_of_isCenteredCounterflowDriver hcf) hlaw
  obtain ⟨h', -, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hgpc hh₂ hcf
  obtain ⟨h'', 𝓕₂, VL₂, VR₂, B₂, -, hC'⟩ := hfl
  have hk' : 0 < 16 / κ := by positivity
  have hbd := counterflowData_bounds hκ (g := g)
    (fun x hx => by
      simp only [hgdef, Sec7.prop74Data, hx, ↓reduceIte]
      nlinarith [Real.pi_pos])
    (fun x hx => by
      simp only [hgdef, Sec7.prop74Data, not_lt.2 hx.le, ↓reduceIte]
      nlinarith [Real.pi_pos])
  have hadm := Sec4.hasAdmissiblePartialSums_flowLine hk'
    (Sec7.StripSysField.isPiecewiseConstant_counterflowData κ hgpc)
    (fun x hx _ => hbd.1 x hx) (fun x hx _ => hbd.2 x hx)
  have hJ : ∀ x ∈ Sec7.StripSysField.counterflowJumps ({0} : Finset ℝ), x = 0 := by
    intro x hx
    simpa [Sec7.StripSysField.counterflowJumps, Sec7.StripSysField.returnExcept] using hx
  have hxL := flowLineXL_eq_zero (g := Sec7.StripSysField.counterflowData κ g) hJ
  have hxR := flowLineXR_eq_zero (g := Sec7.StripSysField.counterflowData κ g) hJ
  have hE := hC'.1
  rw [hxL, hxR] at hadm hE
  exact ⟨_, _, _, _, 𝓕₂, VL₂, VR₂, B₂, hadm, hE⟩

end Word

/-! ### A Borel certificate of a regular, transient trace that does not return to `0` -/

section Cert

variable {nL nR : ℕ}

/-- The norm of the trace read from a history, at a rational time. -/
def trNorm (y : HistorySpace nL nR) (q : ℚ≥0) : ℝ := ‖LP.traceAt (q : ℝ≥0) (hDrv y)‖

theorem measurable_trNorm (q : ℚ≥0) : Measurable fun y : HistorySpace nL nR => trNorm y q :=
  ((LP.measurable_traceAt (q : ℝ≥0)).comp measurable_hDrv).norm

/-- Rational lower bounds of the trace norm on every time interval `[1/(n+1), N]`. -/
def NoZeroCert (y : HistorySpace nL nR) : Prop :=
  ∀ n N : ℕ, ∃ k : ℕ, ∀ q : ℚ≥0, 1 / ((n : ℝ≥0) + 1) ≤ (q : ℝ≥0) → (q : ℝ≥0) ≤ N →
    1 / ((k : ℝ) + 1) ≤ trNorm y q

/-- Rational lower bounds of the trace norm at late times. -/
def TransCert (y : HistorySpace nL nR) : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ q : ℚ≥0, (N : ℝ≥0) ≤ (q : ℝ≥0) → (M : ℝ) ≤ trNorm y q

theorem measurableSet_noZeroCert : MeasurableSet {y : HistorySpace nL nR | NoZeroCert y} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun n => Measurable.forall fun N =>
    Measurable.exists fun k => Measurable.forall fun q => ?_)
  exact Measurable.imp measurable_const (Measurable.imp measurable_const
    (measurableSet_setOfPred.1 (measurableSet_le measurable_const (measurable_trNorm q))))

theorem measurableSet_transCert : MeasurableSet {y : HistorySpace nL nR | TransCert y} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun M => Measurable.exists fun N => Measurable.forall fun q => ?_)
  exact Measurable.imp measurable_const
    (measurableSet_setOfPred.1 (measurableSet_le measurable_const (measurable_trNorm q)))

/-- **Good regular histories**: PROVE-SEC5-Q's good counterflow histories whose trace has the two certificates. -/
def goodRegSet : Set (HistorySpace nL nR) := goodCfSet ∩ {y | NoZeroCert y} ∩ {y | TransCert y}

theorem measurableSet_goodRegSet : MeasurableSet (goodRegSet (nL := nL) (nR := nR)) :=
  (measurableSet_goodCfSet.inter measurableSet_noZeroCert).inter measurableSet_transCert

/-- A rational lower bound on `[a, b]` bounds a continuous curve at every real time of `[a, b)`. -/
theorem le_norm_of_rat {φ : ℝ≥0 → ℂ} (hφ : Continuous φ) {t a b : ℝ≥0} {c : ℝ} (hat : a ≤ t) (htb : t < b)
    (h : ∀ q : ℚ≥0, a ≤ (q : ℝ≥0) → (q : ℝ≥0) ≤ b → c ≤ ‖φ q‖) : c ≤ ‖φ t‖ := by
  have hlim : Tendsto (fun m => ‖φ (Sec7.ratAbove t m)‖) atTop (𝓝 ‖φ t‖) :=
    ((hφ.tendsto t).comp (Sec7.tendsto_ratAbove t)).norm
  refine ge_of_tendsto hlim ?_
  have hb : ∀ᶠ m in atTop, ((Sec7.ratAbove t m : ℚ≥0) : ℝ≥0) < b :=
    (Sec7.tendsto_ratAbove t).eventually (gt_mem_nhds htb)
  filter_upwards [hb] with m hm
  exact h _ (hat.trans (Sec7.le_ratAbove t m)) hm.le

/-- The trace read from a good history is continuous on `[0, ∞)`. -/
theorem continuous_traceAt_of_mem_goodCfSet {y : HistorySpace nL nR} (hy : y ∈ goodCfSet) :
    Continuous fun s : ℝ≥0 => LP.traceAt s (hDrv y) := by
  obtain ⟨⟨_, hcert⟩, htr⟩ := hy
  have hw := hcert.continuous
  have hw0 := hcert.zero
  have hev : ∀ N : ℕ, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (hDrv y) (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) η := by
    intro N
    have h := (Sec7.RandRestart.mem_traceSet_iff hw.continuousOn hw0 fun _ _ =>
      ⟨_, (hw.tendsto _).mono_left nhdsWithin_le_nhds⟩).1 (htr N)
    obtain ⟨η, hη, -⟩ := h
    exact ⟨η, hη⟩
  exact continuousOn_univ.1 ((isGeneratingTrace_top_traceAt hw hw0 hev).2.1.mono
    fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)

/-- **The regularity of a good regular history**: PROVE-SEC5-Q's four properties, no return of the curve to `0` at
positive times, and transience. -/
theorem reg_of_mem_goodRegSet {y : HistorySpace nL nR} (hy : y ∈ goodRegSet) :
    y.1 = ⊤ ∧ Continuous (cfDrv y) ∧ cfDrv y 0 = 0 ∧ IsLoewnerTrace (cfDrv y) (histLine y) ∧
      (∀ u : ℝ, 0 < u → histLine y u ≠ 0) ∧ Tendsto (fun u => ‖histLine y u‖) atTop atTop := by
  obtain ⟨⟨hg, hnz⟩, htc⟩ := hy
  obtain ⟨hζ, hc, h0, hLT⟩ := reg_of_mem_goodCfSet hg
  have hφ := continuous_traceAt_of_mem_goodCfSet hg
  refine ⟨hζ, hc, h0, hLT, fun u hu => ?_, ?_⟩
  · have ht : 0 < u.toNNReal := Real.toNNReal_pos.2 hu
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
    obtain ⟨N, hN⟩ := exists_nat_gt u.toNNReal
    obtain ⟨k, hk⟩ := hnz n N
    have hle := le_norm_of_rat hφ hn.le hN hk
    have hpos : 0 < ‖LP.traceAt u.toNNReal (hDrv y)‖ := lt_of_lt_of_le (by positivity) hle
    rw [histLine_eq_traceAt]
    exact norm_pos_iff.1 hpos
  · refine tendsto_atTop.2 fun M => ?_
    obtain ⟨N, hN⟩ := htc ⌈M⌉₊
    refine eventually_atTop.2 ⟨N, fun u hu => ?_⟩
    have hNu : (N : ℝ≥0) ≤ u.toNNReal := by
      rw [← Real.toNNReal_coe (r := (N : ℝ≥0))]
      exact Real.toNNReal_le_toNNReal (by exact_mod_cast hu)
    have hle := le_norm_of_rat hφ hNu (lt_add_one u.toNNReal) fun q hq _ => hN q hq
    rw [histLine_eq_traceAt]
    exact (Nat.le_ceil M).trans hle

/-- **The history of a continuous driver with a transient generating trace that does not return to `0` is a good
regular history.** -/
theorem cfHistory_mem_goodRegSet {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hζ : ζ ω = ⊤)
    (hw : Continuous fun t => W t ω) (hw0 : W 0 ω = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun t => W t ω) ⊤ η) (hne : ∀ t : ℝ≥0, 0 < t → η t ≠ 0)
    (htr : Tendsto (fun t => ‖η t‖) atTop atTop) : cfHistory W ζ ω ∈ goodRegSet := by
  have hg := cfHistory_mem_goodCfSet hζ hw hw0 hη
  have hval : ∀ p : ℕ × ℕ, dyVal (cfHistory W ζ ω) p = W (dyadicTime p) ω := fun p => by
    simp [dyVal, cfHistory, killedHistory, hζ]
  have hdrv : hDrv (cfHistory W ζ ω) = fun t => W t ω := by
    funext t
    rw [hDrv_apply]
    simp only [hval]
    exact (tendsto_lowerDyadic_of_continuousOn (T := ⊤) hw.continuousOn ENNReal.coe_lt_top).limUnder_eq
  have htrq : ∀ q : ℚ≥0, trNorm (cfHistory W ζ ω) q = ‖η q‖ := fun q => by
    rw [trNorm, hdrv, LP.traceAt_eq_of_isGeneratingTrace hη hw.continuousOn hw0 ENNReal.coe_lt_top]
  have hηc : Continuous η :=
    continuousOn_univ.1 (hη.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
  refine ⟨⟨hg, fun n N => ?_⟩, fun M => ?_⟩
  · by_cases hne' : (Icc (1 / ((n : ℝ≥0) + 1)) (N : ℝ≥0)).Nonempty
    · obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn hne' hηc.norm.continuousOn
      have hpos : 0 < ‖η s‖ := norm_pos_iff.2 (hne s (lt_of_lt_of_le (by positivity) hs.1))
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      refine ⟨k, fun q hq1 hq2 => ?_⟩
      rw [htrq]
      exact hk.le.trans (isMinOn_iff.1 hmin _ ⟨hq1, hq2⟩)
    · exact ⟨0, fun q hq1 hq2 => absurd ⟨q, hq1, hq2⟩ hne'⟩
  · obtain ⟨T, hT⟩ := eventually_atTop.1 (htr.eventually_ge_atTop (M : ℝ))
    obtain ⟨N, hN⟩ := exists_nat_ge T
    exact ⟨N, fun q hq => by rw [htrq]; exact hT _ (hN.trans hq)⟩

end Cert

/-! ### The named input `Prop51Q.CfLineRegularQStatement` -/

/-- **The counterflow line of Proposition 5.5's configuration is regular** (`Prop51Q.CfLineRegularQStatement`;
specification §5, p. 129, and Aux. lemma 7 at `κ′ = 16/κ`), given Zhan's Part A inputs at `16/κ`
(`Sec5.PartAInputsSixteenDiv`, which yields Aux. lemma 7 at `16/κ`): almost surely on the glued space the counterflow
history has infinite lifetime, a continuous driver starting at `0` of which `histLine` is a Loewner trace, and this
curve does not return to `0` at positive times and tends to `∞`. -/
theorem cfLineRegularQStatement_of_partA (hA : PartAInputsSixteenDiv) : Prop51Q.CfLineRegularQStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ hb ha Ω mΩ P _ h hh Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)) :=
    (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  obtain ⟨mL, mR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hadm, hE⟩ :=
    exists_seed_of_isCenteredCounterflowDriver hκ hb ha hh hcf hlaw
  have hk' : 0 < 16 / κ := by positivity
  have hF : IsOrderedForceWord (fun _ : Fin mL => (0 : ℝ)) (fun _ : Fin mR => (0 : ℝ)) :=
    ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  have h7 := aux7Statement_sixteen_div_of_partA.{u} hA hκ hκ4 _ _ σL σR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hF hadm hE
  have hne := ae_trace_ne_zero_of_seed hk' hadm hE (h7.mono fun _ h => h.2.2)
  have hΩ₂ : ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodRegSet := by
    filter_upwards [h7, hne, hE.2.2.2.2] with ω ⟨hζ, ⟨η, hη⟩, htr⟩ hneω hp
    have hw : Continuous fun t => W₂ t ω := by
      have h := hp.2.2.2.1
      rw [hζ] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    exact cfHistory_mem_goodRegSet hζ hw hp.1 hη (hneω η hη) (htr η hη)
  have hg := ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf) (measurable_cfHistory hX₂) hlaw k hk
    measurableSet_goodRegSet hΩ₂
  filter_upwards [hg] with p hp
  exact reg_of_mem_goodRegSet hp

/-- **Proposition 5.1 in the chart `Q` from Zhan's Part A inputs at `16/κ` and the avoidance input**
(PROVE-SEC5-P's `Prop51Q.prop51QStatement_of_cfAvoidLeft` with `cfLineRegularQStatement_of_partA`). -/
theorem prop51QStatement_of_partA_of_cfAvoidLeft (hA : PartAInputsSixteenDiv)
    (havoid : Prop51Q.CfAvoidLeftQStatement.{u}) : Prop51QStatement.{u} :=
  Prop51Q.prop51QStatement_of_cfAvoidLeft (cfLineRegularQStatement_of_partA hA) havoid

end InteractingSLE.Sec5.CfLineRegQ
