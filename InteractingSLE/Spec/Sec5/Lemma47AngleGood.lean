/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma47AngleData
/-!
# Lemma 4.7 at a relative angle: good samples and transience

The existing counterflow admissibility theorem at angle `θ` supplies the same
no-return and transience arguments as the extreme-angle case. No determination input is used.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
universe u
namespace InteractingSLE.Sec5.Lemma47Angle
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q CrossCond.Theta Prop49Exit
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
section NoReturn
variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
theorem ae_cfHistory_mem_nrSet_angle [IsProbabilityMeasure P₂]
    (hNR : CfNoReturn.Route.CounterflowNoReturnAdmStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂) :
    ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ nrSet := by
  -- the counterflow field is a GFF with piecewise constant data
  set c : ℝ := -(θ * chiC κ) with hc
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + c with hbdef
  have hb : IsPiecewiseConstantBoundaryData b (forceJumpFinset xL xR) :=
    isPiecewiseConstant_forceData κ ρL ρR xL xR c
  have hh : IsGFFWithBoundaryData P h (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) := ⟨hC.2.1, hC.2.2.1⟩
  have hh' := isGFFWithBoundaryData_flowField_zero hh c
  rw [← coe_forceJumpFinset] at hh'
  have hh'' : IsGFFWithBoundaryData P (fun ω => cfFieldT κ θ (h ω)) b (forceJumpFinset xL xR) := hh'
  have hh₂ := isGFFWithBoundaryData_of_map_eq hh'' (measurable_of_isCenteredCounterflowDriver hcf) hlaw
  -- infinite lifetime, a continuous driver from `0` and a generating trace, almost surely
  obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
    exists_admissible_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw
  have hk' : 0 < 16 / κ := by positivity
  have htr := ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE
  obtain ⟨hbL, hbR⟩ := hθb
  have hnr := hNR κ hκ hκ4 b (forceJumpFinset xL xR) hb
    (fun x hx _ => hbL x hx)
    (fun x hx _ => hbR x hx) P₂ h₂ hh₂ W₂ ζ₂ hcf
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
theorem ae_isGood47_angle (hNR : CfNoReturn.Route.CounterflowNoReturnAdmStatement.{u}) {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      IsGood47 W VL VR ζ p := by
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
    filter_upwards [hline] with ω hω using hω.1
  have hflow : ∀ᵐ ω ∂P, Aux50Hit.IsGoodPath W VL VR ζ ω ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧ (∀ t : ℝ≥0, 0 < t → η t ∈ H) ∧
        seedLine ζ W ω = fun s : ℝ => η s.toNNReal := by
    filter_upwards [hline, Aux50Hit.ae_isGoodPath hC.1 hζ] with ω ⟨_, ⟨η, hη, he⟩, hP⟩ hg
    refine ⟨hg, η, hη, fun t ht => ?_, he⟩
    have h1 := hP.mem_H t ht
    rw [he] at h1
    simpa only [Real.toNNReal_coe] using h1
  have hfst := ae_glue_fst (μ := P) k hXm hflow
  have hhit := cfGlueAE_mem_goodHitSetT θ κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have hnr : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) hXm), p.2 ∈ Prop49Exit.nrSet :=
    ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf)
      (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)) hlaw k hk
      Prop49Exit.measurableSet_nrSet (ae_cfHistory_mem_nrSet_angle hNR hκ hκ4 hθb hC hcf hlaw)
  filter_upwards [hfst, hhit, hnr] with p h1 h2 h3
  exact ⟨h1.1, h1.2, h2, fun u hu => Prop49Exit.histLine_ne_zero_of_mem_nrSet h3 hu⟩
theorem cfGlueAE_mem_goodTransSet_angle (θ : ℝ) (hA : PartAInputsSixteenDivOfClearance) : CfGlueAET.{u} θ fun _ y => y ∈ goodTransSet := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 hθb Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hΩ₂ : ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodTransSet := by
    obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
      exists_admissible_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw
    have h7 := aux7Statement_sixteen_div_of_partA_of_clearance.{u} hA hκ hκ4 _ _ σL σR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hF' hadm hE
    filter_upwards [h7, hE.2.2.2.2, ae_trace_ne_real_of_isCenteredCounterflowDriverT hκ hθb hC hcf hlaw]
      with ω ⟨hζ, ⟨η, hη⟩, htr⟩ hp hne
    have hw : Continuous fun t => W₂ t ω := by
      have := hp.2.2.2.1
      rw [hζ] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    exact cfHistory_mem_goodTransSet hζ hw hp.1 hη (fun t _ x hx => hne η hη t x hx) (htr η hη)
  exact ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf) (measurable_cfHistory hX₂) hlaw k hk
    measurableSet_goodTransSet hΩ₂


end InteractingSLE.Sec5.Lemma47Angle
