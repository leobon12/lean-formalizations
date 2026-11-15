/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveStage
import InteractingSLE.Spec.Supplement.GW1ActiveThr
import InteractingSLE.Spec.Sec5.Lemma56Stages

/-!
# Lemma GW1's active-word classification: the conditional law of a stage

Packet PROVE-T14-GW1W. Probabilistic inputs of the classification, for a staged history of a field `h` (data `b`)
whose drivers are measurable and regular at every sample:

* `isStopLaw_stopWord`: the single-stage law with the explicit stop word (PROVE-STAGEDLAW3's `stopCondLawStatement`,
  with its word exported);
* `isStageWitness_zero`: the explicit witness at the root (the original word);
* **`ae_isFlowLineDriver_stage`**: at almost every launch, under the regular conditional law given the retained past,
  the driver of the launched piece is the flow-line driver **for the word of the witness** (not only for some datum),
  and the state before the launch is that of the sample.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW1W

open Exist Exist.StagedLaw Exist.Staged Restart LQGMetric

/-- **The single-stage law holds with the stop word** (PROVE-STAGEDLAW3, `stopCondLawStatement`). -/
theorem isStopLaw_stopWord {κ : ℝ} (hκ : 0 < κ) : IsStopLaw.{u} κ (stopWord κ) := by
  refine ⟨measurable_stopWord κ, isSorted_stopWord κ, fun c θ t Ω _ _ Q _ g E hE hreg hfl =>
    ⟨ae_isDrvGood_of_isFlowLineDriver hκ t hreg hfl, fun φ => ?_⟩⟩
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) 0
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  · filter_upwards [ae_condExp_recField_of_inadmissible hκ c θ t Q g E hE hreg hfl hseed φ] with ω h _ using h
  · exact ae_condExp_recField_of_admissible hκ c θ t Q g E hE hreg hfl hseed φ

section Law

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The explicit witness at the root**: the original word, recentred at the root (PROVE-STAGEDLAW's
`stageLaw_zero`, with its witness exported). -/
theorem isStageWitness_zero (hh : IsGFFWithBoundaryData P h b jumps)
    {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    IsStageWitness κ b jumps P h spec E 0 (fun _ => BoundaryWord.shiftW spec.1 c₀)
      (fun ω => flowField spec.1 0 (h ω)) := by
  have hh₀ : IsGFFWithBoundaryData P h c₀.fn c₀.jumps := by
    rw [hc₀J]
    exact (Restart.isGFFWithBoundaryData_congr P h (S := (jumps : Set ℝ)) fun y hy => hc₀ y hy).2 hh
  have hgff := isGFFWithBoundaryData_shiftW spec.1 hh₀
  refine ⟨measurable_const, (measurable_flowField _ _).comp hh.1, Eventually.of_forall fun ω _ => ?_, ?_⟩
  · exact ⟨Chart.isConformal_id.recenter _, Chart.continuousOn_recenter_lift Chart.continuousOn_id_lift,
      isChartTransport_shiftChart _ _ _⟩
  · rw [pastSigma_zero]
    filter_upwards [ae_isGFFWithBoundaryData_condExpKernel_bot hgff] with ω₀ h0 _
    exact h0

/-- **At almost every launch, the piece is the conditional flow line for the word of the witness**, and under the
regular conditional law the state before the launch is that of the sample. -/
theorem ae_isFlowLineDriver_stage (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {ℓ : ℕ} {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E ℓ β Y) :
    ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      (∃ h' : Ω → DistOn upperHalfPlaneOpens, IsFlowLineDriver κ (β ω₀).fn (β ω₀).jumps (instrAngle spec ℓ)
        (condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀) h' (fun t ω => (E ℓ ω).1 t) (fun ω => (E ℓ ω).2)) ∧
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀),
        ExplState.run κ b jumps spec (fun j => E j ω) ℓ = ExplState.run κ b jumps spec (fun j => E j ω₀) ℓ := by
  have h𝒢 : pastSigma κ b jumps spec E ℓ ≤ mΩ := hE.2.1 ℓ
  filter_upwards [hE.2.2.2 ℓ, hW.2.2.1, hW.2.2.2, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hW.2.2.1,
    ae_ae_run_eq runMeasStatement hb spec (k := ℓ) (fun j _ => hE.1 j) (fun j _ => hreg j) (P := P)]
    with ω₀ hstg hp₀ hk₀ hpK hrunK
  intro hl
  refine ⟨?_, hrunK⟩
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hstg c θ' hcθ
  obtain ⟨hspec, -, hc⟩ := eq_launch_of_launches spec _ hcθ
  have hθ' : instrAngle spec ℓ = θ' := by unfold instrAngle; rw [hspec]
  obtain ⟨hconf, hlift, -⟩ := hp₀ hl
  rw [← hc] at hconf hlift
  have hgT : ∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω)
      (Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω)) := fun ω =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ (h ω)
  have hh'e : h' = fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => (hT' ω).unique hconf (hgT ω)
  have hh'm : Measurable h' := by
    rw [hh'e]; exact (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
  have hYe : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀), Y ω = h' ω := by
    filter_upwards [hpK, hrunK] with ω hpω hrω
    have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [launches_run_succ_of_run_eq spec hrω]; exact hl
    obtain ⟨-, -, hT⟩ := hpω hlω
    rw [hrω, ← hc] at hT
    exact hT.unique hconf (hT' ω)
  have hG : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀) h' (β ω₀).fn (β ω₀).jumps :=
    isGFFWithBoundaryData_congr_ae (hk₀ hl) hh'm hYe
  rw [hθ']
  exact ⟨h', isFlowLineDriver_word hκ hG hb' hfl⟩

end Law

/-! ### One stage of the right walk, almost surely -/

section Right

open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ : ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The launch event of instruction `ℓ` is an event of the retained past before `ℓ`. -/
theorem measurableSet_pastSigma_launch (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (ℓ : ℕ) :
    MeasurableSet[pastSigma κ b jumps spec E ℓ]
      {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none} :=
  measurableSet_pastSigma_of_runs runMeasStatement hb (fun j _ => hEm j) (fun j _ => hreg j)
    (measurableSet_launch_self runMeasStatement hb (fun j _ => hEm j) (fun j _ => hreg j))
    fun ω ω' he hω => by
      change (ExplState.run κ b jumps spec (fun j => E j ω') (ℓ + 1)).2.2.2.1 ℓ ≠ none
      rw [← launches_run_succ_of_run_eq spec (he ℓ le_rfl)]
      exact hω

/-- The angle of a launched instruction of a walk is the walk's angle. -/
theorem instrAngle_walk {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {right : Bool} {ℓ : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    instrAngle (boundaryWalkSpec b jumps θ right) ℓ = θ := by
  obtain ⟨hev, hlt⟩ := even_of_launches_walk hl
  unfold instrAngle
  rw [GW1Conn.getElem?_boundaryWalkSpec, ite_eq_left_of_eq_true _ _ (eq_true hlt),
    ite_eq_left_of_eq_true _ _ (eq_true hev)]

/-- The stopped driver of a piece agrees with its driver before the lifetime. -/
theorem stopDrv_top_eq {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {T : ℝ≥0} (hTζ : (T : ℝ≥0∞) = e.2) {r : ℝ} (hr : 0 ≤ r)
    (hrT : r < T) : stopDrv ⊤ e r = e.1 r.toNNReal := by
  have hlt : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < e.2 := by
    rw [← hTζ, ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hr]
    exact hrT
  change e.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min ⊤ e.2)).toNNReal = _
  rw [min_eq_right (le_top : e.2 ≤ ⊤), min_eq_left hlt.le, ENNReal.toNNReal_coe]

theorem stopTime_top_eq {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {T : ℝ≥0} (hTζ : (T : ℝ≥0∞) = e.2) :
    stopTime ⊤ e = (T : ℝ) := by
  unfold stopTime
  rw [min_eq_right (le_top : e.2 ≤ ⊤), ← hTζ, ENNReal.toNNReal_coe]

/-- **One stage of the right walk, almost surely** (Lemma GW1, (GW1.1) and (GW1.3)): if the word of the witness at the
launch `ℓ` satisfies the invariant almost surely at launches, then almost surely a launched piece does not end at a new
left record, has a good record at a finite stop, and leaves a low original height outward of a new right record. -/
theorem ae_stage_right (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ true) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {ℓ : ℕ} {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ true) E ℓ β Y)
    (hinv : ∀ᵐ ω₀ ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        RInv κ θ b jumps (β ω₀) (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω₀) ℓ)) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (ℓ + 1)) ≠
          stThr (some false) ∧
        ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
        (stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (ℓ + 1)) =
            stThr (some true) →
          rightLim b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (ℓ + 1))) +
            θ * chiC κ ≤ -sleLambda κ) := by
  set spec := boundaryWalkSpec b jumps θ true with hspec
  set R : Ω → ℕ → ExplState := fun ω n => ExplState.run κ b jumps spec (fun j => E j ω) n with hRdef
  have h𝒢 : pastSigma κ b jumps spec E ℓ ≤ mΩ := hE.2.1 ℓ
  have hLp := measurableSet_pastSigma_launch (κ := κ) hb spec hE.1 hreg ℓ
  have hMS := isMeasState_run (κ := κ) hb spec hE.1 hreg (ℓ + 1)
  -- the good event is measurable
  set G : Set Ω := {ω | (R ω (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      stStatus (R ω (ℓ + 1)) ≠ stThr (some false) ∧
        ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
        (stStatus (R ω (ℓ + 1)) = stThr (some true) →
          rightLim b (stRecR (R ω (ℓ + 1))) + θ * chiC κ ≤ -sleLambda κ)} with hGdef
  have hGm : MeasurableSet G := by
    have h1 : MeasurableSet {ω | stStatus (R ω (ℓ + 1)) ≠ stThr (some false)} := (hMS.1 _).compl
    have h2 : MeasurableSet {ω | (E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))} := by
      have hζ : Measurable fun ω => (E ℓ ω).2 := measurable_snd.comp (hE.1 ℓ)
      exact ((measurableSet_eq_fun hζ measurable_const).union (measurableSet_good ⊤ (hE.1 ℓ) (hreg ℓ))).congr
        (by ext ω; simp only [mem_union, mem_ofPred_eq]; tauto)
    have h3 : MeasurableSet {ω | stStatus (R ω (ℓ + 1)) = stThr (some true) →
        rightLim b (stRecR (R ω (ℓ + 1))) + θ * chiC κ ≤ -sleLambda κ} := by
      have hm : Measurable fun ω => rightLim b (stRecR (R ω (ℓ + 1))) + θ * chiC κ :=
        ((measurable_rightLim_of_pcbd hb).comp hMS.2.2.2.1).add_const _
      exact ((hMS.1 _).compl.union (measurableSet_le hm measurable_const)).congr
        (by ext ω; simp only [mem_union, mem_compl_iff, mem_ofPred_eq]; tauto)
    exact ((h𝒢 _ hLp).compl.union (h1.inter (h2.inter h3))).congr
      (by ext ω; simp only [mem_union, mem_compl_iff, mem_inter_iff, mem_ofPred_eq, hGdef]; tauto)
  refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hGm ?_
  filter_upwards [ae_isFlowLineDriver_stage hκ hb hh hE hreg hW, hinv,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem h𝒢 hLp.compl] with ω₀ hfl₀ hinv₀ hmemc
  by_cases hl₀ : (R ω₀ (ℓ + 1)).2.2.2.1 ℓ ≠ none
  swap
  · filter_upwards [hmemc hl₀] with ω hω hlω
    exact absurd hlω hω
  obtain ⟨⟨h', hfl⟩, hrunK⟩ := hfl₀ hl₀
  rw [instrAngle_walk hl₀] at hfl
  have hI := hinv₀ hl₀
  have hfl' := hfl
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl'
  have hEv := hC.1
  obtain ⟨cc, hcc, hgc⟩ := GW1Conn.exists_hasGroupEndSums_flowLineL hκ (β ω₀).isPiecewiseConstantBoundaryData hI.1
  have hanti : StrictAnti (flowLineXL (β ω₀).fn (β ω₀).jumps 0) := fun i j hij =>
    GW0.flowLineXL_lt (β ω₀).fn (β ω₀).jumps 0 hij
  filter_upwards [GW1Conn.ae_exists_hit_right hEv hκ hcc hanti.antitone hanti.injective hgc,
    hEv.ae_isIntegratedSLEPath, hEv.ae_tendsto_threshold hκ, ae_isDrvGood_of_isFlowLineDriver hκ ⊤ (hreg ℓ) hfl,
    hrunK] with ω hhit hp hthr hgood hrun hlω
  have hR1 : ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1) =
      ExplState.launch (ExplState.run κ b jumps spec (fun j => E j ω₀) ℓ) ℓ (E ℓ ω) θ ⊤ := by
    rw [launch_walk hlω, hrun]
  rw [hR1]
  -- the hit at a finite positive lifetime, read in the launch chart
  have hhit' : (E ℓ ω).2 ≠ ⊤ → (E ℓ ω).2 ≠ 0 → ∃ y : ℝ, 0 < y ∧
      (∀ r < stopTime ⊤ (E ℓ ω), ∃ u, IsForwardSol (stopDrv ⊤ (E ℓ ω)) (y : ℂ) r u) ∧
      ¬ ∃ u, IsForwardSol (stopDrv ⊤ (E ℓ ω)) (y : ℂ) (stopTime ⊤ (E ℓ ω)) u := by
    intro hD h0
    set T : ℝ≥0 := (E ℓ ω).2.toNNReal with hTdef
    have hTζ : (T : ℝ≥0∞) = (E ℓ ω).2 := ENNReal.coe_toNNReal hD
    have hT : 0 < T := by
      rw [pos_iff_ne_zero]
      intro hT0
      rw [hT0, ENNReal.coe_zero] at hTζ
      exact h0 hTζ.symm
    obtain ⟨y, hy, hyb, hyd⟩ := hhit T hT hTζ (stopDrv ⊤ (E ℓ ω)) fun r hr hrT => stopDrv_top_eq hTζ hr hrT
    rw [stopTime_top_eq hTζ]
    exact ⟨y, hy, hyb, hyd⟩
  refine ⟨launch_ne_thr_false hI.2.1 ℓ θ hhit', fun hD => hgood (min_top_ne_top hD), fun hthr1 => ?_⟩
  -- a right threshold: the outward original height is low
  have hfin : (E ℓ ω).2 ≠ ⊤ := by
    intro htop
    have hmin : min ⊤ (E ℓ ω).2 = ⊤ := by rw [htop]; rfl
    rw [(launch_eq_of_top (R ω₀ ℓ) ℓ (E ℓ ω) θ ⊤ hmin).2.2.2.2.1] at hthr1
    exact absurd hthr1 (by simp)
  obtain ⟨h0, hhitx, -, -⟩ := launch_thr_true hfin hthr1
  have hpos : 0 < (E ℓ ω).2 := pos_iff_ne_zero.2 h0
  have hgd := hgood (min_top_ne_top hfin)
  have hgp : IsGoodStopPath κ (flowLineXL (β ω₀).fn (β ω₀).jumps 0) (flowLineXR (β ω₀).fn (β ω₀).jumps 0)
      (flowLineRhoL κ (β ω₀).fn (β ω₀).jumps 0 θ) (flowLineRhoR κ (β ω₀).fn (β ω₀).jumps 0 θ) ⊤ (E ℓ ω)
      (fun i s => VL i s ω) (fun j s => VR j s ω) (fun s => B s ω) := by
    refine ⟨hp, fun T hT hζ => ?_, hreg ℓ ω, hgd, min_top_ne_top hfin, hpos⟩
    obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hthr T hT hζ
    exact ⟨w₀, vL₀, vR₀, hlim⟩
  obtain ⟨ε, hε, hlow⟩ := lowStart_of_goodStopPath hκ hgp hI.1
  obtain ⟨hs₁, hrel⟩ := rProf_launch hI.2.1 ℓ θ (hreg ℓ ω) hgd hfin hhitx
  have hO := rOrig_of_rel hκ hb hI.2.1 hI.2.2 θ ⟨hs₁, hrel⟩
  exact rightLim_le_of_lowStart hb hs₁ hO hε hlow

end Right

/-! ### The classification at every launch of the right walk -/

section Induction

open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ : ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The own time of a launched instruction of a walk is `⊤`. -/
theorem instrTime_walk {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {right : Bool} {ℓ : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    instrTime (boundaryWalkSpec b jumps θ right) ℓ = ⊤ := by
  obtain ⟨hev, hlt⟩ := even_of_launches_walk hl
  unfold instrTime
  rw [GW1Conn.getElem?_boundaryWalkSpec, ite_eq_left_of_eq_true _ _ (eq_true hlt),
    ite_eq_left_of_eq_true _ _ (eq_true hev)]

/-- The invariant at the root of the right walk (deterministic). -/
theorem rInv_root (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + θ * chiC κ < sleLambda κ) {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps)
    (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    RInv κ θ b jumps (BoundaryWord.shiftW 0 c₀) (ExplState.init 0) ∧ RReady (ExplState.init 0) ∧
      leftLim b 0 + θ * chiC κ < sleLambda κ := by
  have hprof : rProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    simp [rProf, ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hR : stRecR (ExplState.init 0) = 0 := rfl
  have hJ : ∀ y, y ∉ (BoundaryWord.shiftW 0 c₀).jumps → y ∉ jumps := fun y hy h => hy (by
    rw [BoundaryWord.jumps_shiftW, hc₀J]
    exact Finset.mem_image.2 ⟨y, h, by ring⟩)
  refine ⟨⟨fun y hy hyJ => ?_, ⟨fun x => ?_, ?_, fun x hx => ?_, fun ε hε => ?_⟩, fun x hx hxJ hzJ => ?_⟩,
    ⟨Or.inl rfl, rfl⟩, ?_⟩
  · rw [BoundaryWord.fn_shiftW, add_zero, hc₀ y (hJ y hyJ)]
    exact hamb y hy (hJ y hyJ)
  · simp [ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  · rw [hprof, hR]
    exact ⟨strictMonoOn_id, continuousOn_id, fun M => ⟨max M 0 + 1, by positivity, by
      linarith [le_max_left M 0]⟩⟩
  · rw [hprof]; rw [hR] at hx; exact hx
  · rw [hprof, hR]; exact ⟨ε / 2, half_pos hε, by linarith⟩
  · rw [hprof] at hzJ ⊢
    rw [BoundaryWord.fn_shiftW, add_zero]
    exact hc₀ x hxJ
  · obtain ⟨lo, hlo, hconst⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_leftLim hb 0
    have hne : (Ioo lo (0 : ℝ) \ (jumps : Set ℝ)).Nonempty := by
      have hinf : (Ioo lo (0 : ℝ)).Infinite := Ioo_infinite hlo
      exact (hinf.sdiff jumps.finite_toSet).nonempty
    obtain ⟨t, ht, htJ⟩ := hne
    rw [← hconst t ht]
    exact hamb t ht.2 htJ

/-- **GW1's active-word classification for the right walk** (Lemma GW1, p. 619–620): for a staged right walk with
measurable drivers regular at every sample, at every instruction `k` the staged conditional law has a witness whose
word, almost surely at a launch at `k`, is admissible left of the seed and is the original word, read in the chart, on
the untouched ray right of the right record (`RInv`), the state being launch-ready. -/
theorem exists_witness_right (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ true) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + θ * chiC κ < sleLambda κ) :
    ∀ k, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ true) E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠
          none →
        RInv κ θ b jumps (β ω) (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) ∧
        RReady (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) ∧
        (stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) = .inl () →
          leftLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k)) +
            θ * chiC κ < sleLambda κ) := by
  set spec := boundaryWalkSpec b jumps θ true with hspec
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀, fun ω => flowField spec.1 0 (h ω),
        isStageWitness_zero hh hc₀J hc₀, Eventually.of_forall fun ω _ => ?_⟩
      have h0 := rInv_root (κ := κ) (θ := θ) hb hamb hc₀J hc₀
      exact ⟨h0.1, h0.2.1, fun _ => h0.2.2⟩
    have H : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens), ℓ < k →
        IsStageWitness κ b jumps P h spec E ℓ β Y ∧
        ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          RInv κ θ b jumps (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          RReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
            leftLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ < sleLambda κ) := by
      intro ℓ
      by_cases hℓ : ℓ < k
      · obtain ⟨β, Y, hW, hI⟩ := ih ℓ hℓ
        exact ⟨β, Y, fun _ => ⟨hW, hI⟩⟩
      · exact ⟨fun _ => default, fun _ => 0, fun h' => absurd h' hℓ⟩
    choose β Y hWI using H
    obtain ⟨βk, Yk, hWk, hexpl⟩ := isStageWitness_succ_expl (isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
      hk (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j) β Y fun ℓ hℓ => (hWI ℓ hℓ).1
    refine ⟨βk, Yk, hWk, ?_⟩
    have hstage : ∀ ℓ, ℓ < k → ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) ≠ stThr (some false) ∧
          ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) = stThr (some true) →
            rightLim b (stRecR (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) + θ * chiC κ ≤
              -sleLambda κ) := fun ℓ hℓ =>
      ae_stage_right hκ hb hh hE hreg (hWI ℓ hℓ).1 ((hWI ℓ hℓ).2.mono fun ω hω hl => (hω hl).1)
    have hall : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
        ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          RInv κ θ b jumps (β ℓ ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          RReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
            leftLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ < sleLambda κ)) ∧
        ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) ≠ stThr (some false) ∧
          ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
          (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) = stThr (some true) →
            rightLim b (stRecR (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) + θ * chiC κ ≤
              -sleLambda κ)) := by
      refine ae_all_iff.2 fun ℓ => ?_
      by_cases hℓ : ℓ < k
      · filter_upwards [(hWI ℓ hℓ).2, hstage ℓ hℓ] with ω h1 h2 _ using ⟨h1, h2⟩
      · exact Eventually.of_forall fun ω h' => absurd h' hℓ
    filter_upwards [hall] with ω hω hlk
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
    obtain ⟨ℓ, hℓk, ⟨c', θ'', hl'⟩, -, hn, -⟩ := exists_last_launch spec (fun j => E j ω) hk hcθ
    have hl : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rw [hl']; simp
    obtain ⟨hinv, hst⟩ := hω ℓ hℓk
    obtain ⟨hI, hR, hroot⟩ := hinv hl
    obtain ⟨hnoL, hgood, hF2⟩ := hst hl
    obtain ⟨hInv, hReady, ha⟩ := rInv_walk_step (D := fun j => E j ω) hκ hb hℓk hlk hl hn hI hR hroot (hreg ℓ ω)
      hgood hnoL hF2
    have hβ := hexpl ℓ ω hℓk hlk hl hn
    rw [instrAngle_walk hl, pastMap_last_of_launch hl, instrTime_walk hl, ← ha] at hβ
    rw [hβ]
    refine ⟨hInv, hReady, fun hroot' => ?_⟩
    obtain ⟨-, -, r, hr⟩ := run_eq_of_last_launch (D := fun j => E j ω) hℓk hlk hl hn
    rw [hr] at hroot'
    exact absurd hroot' (by simp [stArcM])

end Induction

end GW1W

end Theorem14

end InteractingSLE
