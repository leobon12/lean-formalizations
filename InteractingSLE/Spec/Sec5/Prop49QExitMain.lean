/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop49QExitMainPull
import InteractingSLE.Spec.Supplement.GW4Completion

/-!
# Proposition 4.9's first exit in the chart `Q` (`Prop411Q.Prop49QExitStatement`)

Packet PROVE-GLUECOND11 (G6 of Proposition 4.9's direction; specification §4.2, proof of Proposition 4.9, Remark 4.10
and Aux. lemma 22, pp. 113–121; ruling R59). **`prop49QExitStatement_of_noReturn`**: the named input
`Prop411Q.Prop49QExitStatement` holds as soon as centred counterflows do not return to their start
(`Theorem14.GW4Ident.CounterflowNoReturnStatement`, PROVE-T14-GW4T5's target; R59 keeps it a hypothesis).

## Proof

On the glued space of `Prop411Q.CfGlueAE`, at a positive rational counterflow time `s`:

1. almost every sample is good (`CrossCond.Word49.cfGlueAE_isGood49`), and its counterflow history has a continuous
   driver with a continuous Loewner trace (`CfRegQ.reg_of_mem_goodCfSet`);
2. the image word of the flow line in the counterflow chart exits at a finite capacity, at a point of `ℍ` or at a real
   point left of the left junction (`ae_imgExit`: PROVE-GLUECOND10's martingale clause, PROVE-GLUECOND7's word
   entrance, Aux. lemma 22 for the left span with coincident marks merged);
3. the counterflow's trace does not return to `0` (`CounterflowNoReturnStatement`, transferred to the glued space
   through a countable Borel coding of "no return", `nrSet`);
4. the deterministic pull-back `exit_of_imgExit` gives the first contact and the left-side limit.

No result here uses Theorem 1.2, Theorem 1.3, `Theorem12ParamStatement` or `Theorem13Statement` (R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop49Exit

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord CrossCond CrossCond.Word49 MartChar.RealFlow LawUnique Cond44Ref Prop411Q CfRegQ

/-! ### The Borel set of histories whose trace does not return to `0` -/

section NoReturn

/-- **Histories whose trace does not return to `0`**, coded by countably many conditions: a good counterflow
history (`CfRegQ.goodCfSet`) whose measurable trace stays at a rational positive distance from `0` at the rational
times of every `[1/(n+1), n+1]`. -/
def nrSet : Set (HistorySpace 0 0) :=
  goodCfSet ∩ {y | ∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ≥0, 1 / ((n : ℝ) + 1) ≤ ((q : ℝ≥0) : ℝ) →
    ((q : ℝ≥0) : ℝ) ≤ (n : ℝ) + 1 → 1 / ((m : ℝ) + 1) ≤ ‖LP.traceAt (q : ℝ≥0) (hDrv y)‖}

theorem measurableSet_nrSet : MeasurableSet nrSet := by
  refine measurableSet_goodCfSet.inter (measurableSet_setOfPred.2 (Measurable.forall fun n =>
    Measurable.exists fun m => Measurable.forall fun q => Measurable.imp measurable_const
      (Measurable.imp measurable_const ?_)))
  exact measurableSet_setOfPred.1 (measurableSet_le measurable_const
    ((LP.measurable_traceAt _).comp measurable_hDrv).norm)

/-- The trace read from a good history is continuous on `[0, ∞)`. -/
theorem continuous_traceAt_of_mem_goodCfSet {y : HistorySpace 0 0} (hy : y ∈ goodCfSet) :
    Continuous fun t : ℝ≥0 => LP.traceAt t (hDrv y) := by
  obtain ⟨⟨-, hc⟩, htr⟩ := hy
  have hw := hc.continuous
  have hw0 := hc.zero
  have hev : ∀ N : ℕ, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (hDrv y) (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) η := by
    intro N
    obtain ⟨η, hη, -⟩ := (Sec7.RandRestart.mem_traceSet_iff hw.continuousOn hw0 fun _ _ =>
      ⟨_, (hw.tendsto _).mono_left nhdsWithin_le_nhds⟩).1 (htr N)
    exact ⟨η, hη⟩
  have hgen := isGeneratingTrace_top_traceAt hw hw0 hev
  exact continuousOn_univ.1 (hgen.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)

/-- **On `nrSet` the trace does not return to `0`.** -/
theorem histLine_ne_zero_of_mem_nrSet {y : HistorySpace 0 0} (hy : y ∈ nrSet) {v : ℝ} (hv : 0 < v) :
    histLine y v ≠ 0 := by
  obtain ⟨hyg, hnr⟩ := hy
  have hc := continuous_traceAt_of_mem_goodCfSet hyg
  set v' : ℝ≥0 := v.toNNReal with hv'
  have hv'v : (v' : ℝ) = v := Real.coe_toNNReal _ hv.le
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / ((n : ℝ) + 1) < v ∧ v < (n : ℝ) + 1 := by
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hv
    obtain ⟨n₂, hn₂⟩ := exists_nat_gt v
    refine ⟨max n₁ n₂, lt_of_le_of_lt ?_ hn₁, lt_of_lt_of_le hn₂ ?_⟩
    · exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right (le_max_left _ _) 1)
    · have : (n₂ : ℝ) ≤ (max n₁ n₂ : ℕ) := by exact_mod_cast le_max_right _ _
      linarith
  obtain ⟨m, hm⟩ := hnr n
  intro h0
  have h0' : LP.traceAt v' (hDrv y) = 0 := by rw [histLine_eq_traceAt] at h0; exact h0
  -- near `v` the trace is small; pick a rational time there
  have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have hev : ∀ᶠ t in 𝓝 v', ‖LP.traceAt t (hDrv y)‖ < 1 / ((m : ℝ) + 1) := by
    have := (continuous_norm.comp hc).continuousAt (x := v')
    have h1 : ‖LP.traceAt v' (hDrv y)‖ < 1 / ((m : ℝ) + 1) := by rw [h0', norm_zero]; exact hpos
    exact this.eventually (gt_mem_nhds h1)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set a := max (1 / ((n : ℝ) + 1)) (v - δ) with ha
  set b := min ((n : ℝ) + 1) (v + δ) with hb
  have hab : a < b := by
    rw [ha, hb]
    refine max_lt (lt_min (by linarith [hn.1, hn.2]) (by linarith)) (lt_min (by linarith [hn.2]) (by linarith))
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hab
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hr0 : (0 : ℝ) ≤ r := le_of_lt (lt_trans ha0 hr1)
  set q : ℚ≥0 := r.toNNRat with hq
  have hqr : ((q : ℝ≥0) : ℝ) = r := by
    have e : ((q : ℝ≥0) : ℝ) = ((q : ℚ) : ℝ) := by norm_cast
    rw [e, hq, Rat.coe_toNNRat r (by exact_mod_cast hr0)]
  have hq1 : 1 / ((n : ℝ) + 1) ≤ ((q : ℝ≥0) : ℝ) := by rw [hqr]; exact (le_max_left _ _).trans hr1.le
  have hq2 : ((q : ℝ≥0) : ℝ) ≤ (n : ℝ) + 1 := by rw [hqr]; exact hr2.le.trans (min_le_left _ _)
  have hqd : dist (q : ℝ≥0) v' < δ := by
    rw [NNReal.dist_eq, hqr, hv'v, abs_lt]
    constructor
    · linarith [le_max_right (1 / ((n : ℝ) + 1)) (v - δ)]
    · linarith [min_le_right ((n : ℝ) + 1) (v + δ)]
  have := hm q hq1 hq2
  linarith [hball hqd]

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The counterflow's history lies in `nrSet` almost surely**, given that centred counterflows do not return to
their start. -/
theorem ae_cfHistory_mem_nrSet [IsProbabilityMeasure P₂]
    (hNR : Theorem14.GW4Ident.CounterflowNoReturnStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂) :
    ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ nrSet := by
  -- the counterflow field is a GFF with piecewise constant data
  set c : ℝ := -(π / 2 * chiC κ) with hc
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + c with hbdef
  have hb : IsPiecewiseConstantBoundaryData b (forceJumpFinset xL xR) :=
    isPiecewiseConstant_forceData κ ρL ρR xL xR c
  have hh : IsGFFWithBoundaryData P h (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) := ⟨hC.2.1, hC.2.2.1⟩
  have hh' := isGFFWithBoundaryData_flowField_zero hh c
  rw [← coe_forceJumpFinset] at hh'
  have hh'' : IsGFFWithBoundaryData P (fun ω => cfField κ (h ω)) b (forceJumpFinset xL xR) := hh'
  have hh₂ := isGFFWithBoundaryData_of_map_eq hh'' (measurable_of_isCenteredCounterflowDriver hcf) hlaw
  -- infinite lifetime, a continuous driver from `0` and a generating trace, almost surely
  obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
    exists_admissible_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw
  have hk' : 0 < 16 / κ := by positivity
  have htr := ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE
  have hζ : ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ := by filter_upwards [htr] with ω h; exact h.1
  have hnr := hNR κ hκ hκ4 b (forceJumpFinset xL xR) hb P₂ h₂ hh₂ W₂ ζ₂ hcf hζ
  filter_upwards [htr, hE.2.2.2.2, hnr] with ω ⟨hζω, _, η, hη⟩ hp hnrω
  have hw : Continuous fun t => W₂ t ω := by
    have := hp.2.2.2.1
    rw [hζω] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  have hgood := cfHistory_mem_goodCfSet hζω hw hp.1 hη
  refine ⟨hgood, fun n => ?_⟩
  -- the driver read from the history is the counterflow driver
  have hval : ∀ p : ℕ × ℕ, dyVal (cfHistory W₂ ζ₂ ω) p = W₂ (dyadicTime p) ω := fun p => by
    simp [dyVal, cfHistory, killedHistory, hζω]
  have hdrv : hDrv (cfHistory W₂ ζ₂ ω) = fun t => W₂ t ω := by
    funext t
    rw [hDrv_apply]
    simp only [hval]
    exact (tendsto_lowerDyadic_of_continuousOn (T := ⊤) hw.continuousOn ENNReal.coe_lt_top).limUnder_eq
  have hc' := continuous_traceAt_of_mem_goodCfSet hgood
  have hgen : IsGeneratingTrace (fun t => W₂ t ω) ⊤ fun t => LP.traceAt t (hDrv (cfHistory W₂ ζ₂ ω)) := by
    have hev : ∀ N : ℕ, ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₂ t ω)
        (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) η' := fun N =>
      ⟨η, hη.1, hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top, fun t _ => hη.2.2 t ENNReal.coe_lt_top⟩
    rw [hdrv]
    exact isGeneratingTrace_top_traceAt hw hp.1 hev
  have hne := hnrω _ hgen
  -- a positive lower bound on the compact `[1/(n+1), n+1]`
  set K : Set ℝ≥0 := Icc ((1 / ((n : ℝ) + 1)).toNNReal) (((n : ℝ) + 1).toNNReal) with hK
  have hKne : K.Nonempty := ⟨((n : ℝ) + 1).toNNReal, by
    refine ⟨Real.toNNReal_le_toNNReal ?_, le_rfl⟩
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]⟩
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hKne
    ((continuous_norm.comp hc').continuousOn (s := K))
  have ht₀0 : 0 < t₀ := lt_of_lt_of_le (Real.toNNReal_pos.2 (by positivity)) ht₀.1
  have hpos : 0 < ‖LP.traceAt t₀ (hDrv (cfHistory W₂ ζ₂ ω))‖ := norm_pos_iff.2 (hne t₀ ht₀0)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  refine ⟨m, fun q hq1 hq2 => hm.le.trans (hmin ⟨?_, ?_⟩)⟩
  · exact Real.toNNReal_le_iff_le_coe.2 hq1
  · exact (Real.le_toNNReal_iff_coe_le (by positivity)).2 hq2

end NoReturn

/-! ### Proposition 4.9's first exit -/

section Main

/-- **Proposition 4.9's first exit at a rational counterflow time, in the chart `Q`** (`Prop411Q.Prop49QExitStatement`;
specification p. 120, Remark 4.10 and Aux. lemma 22), from the no-return of centred counterflows to their start
(ruling R59: the source leaves it implicit; PROVE-T14-GW4T5's target `CounterflowNoReturnStatement`). -/
theorem prop49QExitStatement_of_noReturn (hNR : Theorem14.GW4Ident.CounterflowNoReturnStatement.{u}) :
    Prop49QExitStatement.{u} := by
  intro s hs κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set s' : ℝ≥0 := (s : ℝ).toNNReal with hs'def
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs' : 0 < s' := Real.toNNReal_pos.2 hs0
  have hss' : (s' : ℝ) = (s : ℝ) := Real.coe_toNNReal _ hs0.le
  set E := glueGood μ s' ζ W with hEdef
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hgood := cfGlueAE_isGood49 s' hs' κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have hae : ∀ᵐ p ∂μ, IsGood49 s' ζ W p := by
    filter_upwards [hgood] with p hp
    exact isGood49_of_mem hp.1 hp.2
  have hexit := ae_imgExit hκ hκ4 hF h44 hC hcf hlaw k hk hs'
  have hnr : ∀ᵐ p ∂μ, p.2 ∈ nrSet :=
    ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf)
      (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)) hlaw k hk
      measurableSet_nrSet (ae_cfHistory_mem_nrSet hNR hκ hκ4 hF h44 hC hcf hlaw)
  filter_upwards [hexit, hgood, hnr, ae_mem_glueGood hae] with p ⟨hTne, z, hz, hzalt⟩ hpg hpnr hpE
  obtain ⟨hα, hG0, hjL0, -, hQ⟩ := isGood49_of_mem_glueGood p hpE
  have hy : p.2 ∈ goodCfSet := hpg.2.1.1
  obtain ⟨-, hw, hw0, hβ⟩ := reg_of_mem_goodCfSet hy
  -- from the stopped driver `cfDrv0` to the counterflow driver `cfDrv`
  have hEq := eqOn_cfDrv0_cfDrv hy s'
  have hK0 := fwdHull_cfDrv0 hy s'
  have hR0 := revChart_cfDrv0 hy s'
  have hrI : rightImg (cfDrv0 s' p.2) 0 s' = rightImg (cfDrv p.2) 0 s' :=
    Sec7.Lemma71B.rightImg_congr hw s'.coe_nonneg hEq 0
  have hw0s : cfDrv0 s' p.2 s' = cfDrv p.2 s' := hEq s' ⟨s'.coe_nonneg, le_rfl⟩
  have hjL : 0 < rightImg (cfDrv p.2) 0 s - cfDrv p.2 s := by
    rw [← hss', ← hrI, ← hw0s]; exact hjL0
  have hG : IsClosed (negInv '' fwdHull (cfDrv p.2) s) := by rw [← hss', ← hK0]; exact hG0
  have hcurve : gCurve s' ζ W E p = imgCurve (cfDrv p.2) s (seedLine ζ W p.1) := by
    rw [gCurve_of_mem hpE]
    funext u
    simp only [imgCurve]
    rw [hR0, hss']
  have hpre : gPre s' ζ W E p = preContact (seedLine ζ W p.1) (negInv '' fwdHull (cfDrv p.2) s) := by
    rw [gPre_of_mem hpE, hQ, hK0, hss']
  have hjun : gXL xL s' E p (Fin.last nL) = junL (cfDrv p.2) s := by
    rw [gXL_of_mem hpE, Fin.snoc_last]
    simp only [junL]
    rw [hrI, hw0s, hss']
  have hT' : ((ENNReal.toNNReal (imgT s' ζ W E p) : ℝ≥0) : WithTop ℝ≥0) =
      kLife (imgCurve (cfDrv p.2) s (seedLine ζ W p.1))
        (preContact (seedLine ζ W p.1) (negInv '' fwdHull (cfDrv p.2) s)) := by
    rw [← hcurve, ← hpre]
    exact ENNReal.coe_toNNReal hTne
  have hz' : Tendsto (kTrace (imgCurve (cfDrv p.2) s (seedLine ζ W p.1))
      (preContact (seedLine ζ W p.1) (negInv '' fwdHull (cfDrv p.2) s)))
      (𝓝[<] ENNReal.toNNReal (imgT s' ζ W E p)) (𝓝 z) := by
    rw [← hcurve, ← hpre]; exact hz
  have hzalt' : z ∈ H ∨ ∃ x₀ : ℝ, x₀ < junL (cfDrv p.2) s ∧ z = x₀ := by
    rcases hzalt with h1 | ⟨x₀, hx₀, rfl⟩
    · exact Or.inl h1
    · exact Or.inr ⟨x₀, hjun ▸ hx₀, rfl⟩
  have hNRp : ∀ v ∈ Ioc (0 : ℝ) s, histLine p.2 v ≠ 0 := fun v hv =>
    histLine_ne_zero_of_mem_nrSet hpnr hv.1
  obtain ⟨t₀, x₀, ht₀, hx₀, ⟨v, hv, hve⟩, havoid, hlim⟩ :=
    exit_of_imgExit hw hw0 hβ hs0 hNRp hjL hG hα hT' hz' hzalt'
  exact ⟨t₀, x₀, ht₀, hx₀, ⟨v, hv, hve⟩, havoid, hlim⟩

/-- **Proposition 4.11 in the chart `Q`** (`Cond44Ref.Prop411QStatement`) from Lemma 4.7 at rational flow times and the
no-return of centred counterflows (the counterflow's regularity is `CfRegQ.cfRegQStatement`). Conditional helper. -/
theorem prop411QStatement_of_lemma47Q_of_noReturn (h47 : Lemma47QHitStatement.{u})
    (hNR : Theorem14.GW4Ident.CounterflowNoReturnStatement.{u}) : Prop411QStatement.{u} :=
  prop411QStatement_of_lemma47Q_of_prop49Q cfRegQStatement h47 (prop49QExitStatement_of_noReturn hNR)

end Main

end InteractingSLE.Sec5.Prop49Exit
