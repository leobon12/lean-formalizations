/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleCode
import InteractingSLE.Spec.Supplement.GW2JointKernelProofChart

/-!
# The marked conditional field at the next finite schedule instruction

The update retains the whole past. Its Gaussian law is `post_stage`, with the
actual stop word, and its chart is the composition with the actual record chart.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Prop513TreeExtract QuantumZipper

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → Driver}

theorem stageWitness_zero (s : Schedule) (c : BoundaryWord)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) :
    IsStageWitness κ c.fn c.jumps P h (scheduleSpec s) E 0 (fun _ => c) h := by
  refine ⟨measurable_const, hh.1, Eventually.of_forall fun ω _ => ?_, ?_⟩
  · change (Chart.id.recenter 0).IsConformal ∧
      ContinuousOn (fun w => (Chart.id.recenter 0).2.2 ((Chart.id.recenter 0).2.1 w)) H ∧
      IsChartTransport (Chart.id.recenter 0) 1 0 (chiC κ) (h ω) (h ω)
    rw [Chart.recenter_zero]
    refine ⟨Chart.isConformal_id, Chart.continuousOn_id_lift, ?_⟩
    have ht := isChartTransport_shiftChart 0 (chiC κ) (h ω)
    simpa only [Prop74B.flowField_zero_zero, shiftChart, Chart.recenter_zero] using ht
  · rw [pastSigma_zero]
    exact (ae_isGFFWithBoundaryData_condExpKernel_bot hh).mono fun _ hω _ => hω

/-- The next actual marked conditional field, retaining all earlier pieces. -/
theorem stageWitness_succ (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (s : Schedule) (hE : IsStagedHistory κ b J P h (scheduleSpec s) E)
    (hr : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    (hk : k < (scheduleSpec s).2.2.length)
    (hTop : ∀ᵐ ω ∂P, ∀ j < k + 1, (E j ω).2 = ⊤)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hw : IsStageWitness κ b J P h (scheduleSpec s) E k β Y) :
    let R := fun ω => pastMap κ b J (scheduleSpec s) E (k + 1) ω (Fin.last k)
    IsStageWitness κ b J P h (scheduleSpec s) E (k + 1)
      (fun ω => stopWord κ (β ω, instrAngle (scheduleSpec s) k, R ω))
      (fun ω => recField κ (R ω) (Y ω)) := by
  let spec := scheduleSpec s
  let R := fun ω => pastMap κ b J spec E (k + 1) ω (Fin.last k)
  have hpm := measurable_pastMap (κ := κ) runMeasStatement hb spec (fun j _ => hE.1 j)
    (fun j _ => hr j) (k + 1) le_rfl
  have h𝒢 : pastSigma κ b J spec E (k + 1) ≤ mΩ := hE.2.1 _
  have hRm : Measurable R := (measurable_pi_apply (Fin.last k)).comp hpm
  have hRp : Measurable[pastSigma κ b J spec E (k + 1)] R := by
    rw [pastSigma_eq_comap]
    exact (measurable_pi_apply (X := fun _ : Fin (k + 1) => RecData) (Fin.last k)).comp
      (comap_measurable _)
  have hβp : Measurable[pastSigma κ b J spec E (k + 1)] β :=
    hw.1.mono (pastSigma_mono spec E (Nat.le_succ k)) le_rfl
  have hβm : Measurable[pastSigma κ b J spec E (k + 1)]
      (fun ω => stopWord κ (β ω, instrAngle spec k, R ω)) :=
    (measurable_stopWord κ).comp (hβp.prodMk (measurable_const.prodMk hRp))
  have hYm : Measurable (fun ω => recField κ (R ω) (Y ω)) :=
    measurable_recField_comp κ hRm hw.2.1
  have hlaunch : ∀ᵐ ω ∂P,
      (ExplState.run κ b J spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none :=
    hTop.mono fun ω hω => launch_of_previous_top s _ hk (fun j hj => hω j (by omega))
  have hR : ∀ᵐ ω ∂P, R ω = recOf (instrTime spec k) (E k ω) :=
    hlaunch.mono fun _ hl => pastMap_last_of_launch hl
  have hpost := post_stage (StripSideHeightProb.isStopLaw_stopWord hκ)
    runMeasStatement hκ hb hh (fun j _ => hE.1 j) (fun j _ => hr j) (hE.2.2.2 k)
    hw.1 hw.2.1 hw.2.2.1 hw.2.2.2
  refine ⟨hβm, hYm, ?_, ?_⟩
  · filter_upwards [hw.2.2.1, hTop, hlaunch, hR] with ω hp ht hl he _
    obtain ⟨hc, hℓ, hT⟩ := hp hl
    have hfin : min (instrTime spec k) (E k ω).2 ≠ ⊤ :=
      ne_top_of_le_ne_top (instrTime_finite s hk) (min_le_left _ _)
    have hgood : LocalExt.IsDrvGood (recHist (recOf (instrTime spec k) (E k ω))) := by
      have htime : ((instrTime spec k).toNNReal : ℝ≥0∞) < (E k ω).2 := by
        rw [ht k (Nat.lt_succ_self k)]
        exact ENNReal.coe_lt_top
      have hg := isDrvGood_recOf_of_lt (hr k ω) htime
      rw [ENNReal.coe_toNNReal (instrTime_finite s hk)] at hg
      exact hg
    have ha := active_run (κ := κ) (b := b) (J := J) s (fun j => E j ω) k hk.le
      (fun j hj => ht j (by omega))
    have hchart : (ExplState.run κ b J spec (fun j => E j ω) (k + 1)).2.2.2.2.1 =
        (ExplState.run κ b J spec (fun j => E j ω) k).2.2.2.2.1.trans (recChart (R ω)) := by
      rw [run_succ_of_active s _ hk ha, chart_launch _ _ _ _ _ hfin, he,
        recChart_eq_loewner (hr k ω) hgood, Chart.loewner_eq_trans]
      rfl
    rw [hchart]
    refine ⟨hc.trans (isConformal_recChart _),
      Theorem14.GW2JointKernel.continuousOn_trans_lift hc (isConformal_recChart _)
        hℓ (continuousOn_recChart_lift _), ?_⟩
    exact IsChartTransport.trans hc (isConformal_recChart _) hℓ
      (continuousOn_recChart_lift _) hT (isChartTransport_recField κ _ _)
  · have hCF : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) →
        P[fun ω' => Complex.exp (Complex.I * (recField κ (R ω') (Y ω') φ : ℂ)) |
          pastSigma κ b J spec E (k + 1)] ω =
          gaussCF (stopWord κ (β ω, instrAngle spec k, R ω)) φ := by
      intro φ
      filter_upwards [hpost.2 φ, hlaunch] with ω hω hl _
      exact hω hl (ne_top_of_le_ne_top (instrTime_finite s hk) (min_le_left _ _))
    have hg := ae_isGFFWithBoundaryData_condExpKernel h𝒢 (M := univ)
      (Eventually.of_forall fun ω _ => isSorted_stopWord κ _) hYm hCF
    exact hg.mono fun _ hω _ => hω (mem_univ _)

end InteractingSLE.Sec5.Prop513Schedule
