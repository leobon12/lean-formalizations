/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59SchedReal
import InteractingSLE.Spec.Sec5.Prop513SchedulePieces
import InteractingSLE.Spec.Exist.StagedLaw4Def

/-!
# Fixed extreme-angle schedules realized as staged histories on the field's own space (R48-safe)

Packet PROVE-PROP59-SCHED: Theorem 1.2's Proposition 5.13 input (B) (`planning/handoffs/PROVE-PROP513-ASM.md` §3),
by the route of Astra's follow-up 5 §2.1 (ruling R73): every piece of a fixed extreme-angle schedule is determined by
the conditional field, and finite induction gives determination by the original field. Here the determination runs
**forward**: the staged history of a schedule `s` is *defined* as the Borel recursion of the field
(`Prop513Schedule.codeDriver`, the direct/reflected §4.2 determination maps of `Theorem12ParamCond44Statement`), and is
shown to satisfy the frozen `IsStagedHistory` and the R51 regularity `StagedPiecesRegular`.

* **`schedDrivers`**: `j, ω ↦ codeDriver h44 c (scheduleSpec s) j (h ω)`;
* **`stageWitness_succ_of_stageOK`**: PROVE-PROP513's `stageWitness_succ` with only the stage-`k` flow-line clause
  (`StageOK`) in place of the whole staged history (the induction needs it before the history is known);
* **`stageOK_schedDrivers`**: given the marked conditional field at stage `k` (`IsStageWitness`, with the actual
  context equal to the code context), stage `k` is a conditional flow line: under `condExpKernel P (pastSigma k) ω₀`
  the field read in the stage chart is a GFF with the extreme-height word `β ω₀`, and the stage driver is a.s.
  `stageDriver θ_k (β ω₀, ·)` of it, which is a flow-line driver (`Prop59Sched.isFlowLineDriver_stageDriver`);
* **`schedDrivers_induction`**, **`isStagedHistory_schedDrivers`**, **`stagedPiecesRegular_schedDrivers`**, and
  **`exists_schedule_stagedHistories`** (one family `E : Schedule → ℕ → Ω → Driver` for all schedules at once).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `h12p`, `h13` or any
`*_of_param`; the only named input is `Theorem12ParamCond44Statement` (R74).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop59Sched

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.AdmCode Sec7.StripWall Prop513Schedule Prop513TreeExtract QuantumZipper

section Defs

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)

/-- **The canonical staged drivers of the schedule `s`**: the Borel recursion of the field (direct/reflected §4.2
determination maps along the actual stop words and record fields). -/
def schedDrivers (c : BoundaryWord) (s : Schedule) {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) :
    ℕ → Ω → Driver :=
  fun j ω => codeDriver h44 hκ hκ4 c (scheduleSpec s) j (h ω)

theorem measurable_schedDrivers (c : BoundaryWord) (s : Schedule) {Ω : Type*} [MeasurableSpace Ω]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (j : ℕ) :
    Measurable (schedDrivers h44 hκ hκ4 c s h j) :=
  (measurable_codeDriver h44 hκ hκ4 c (scheduleSpec s) j).comp hh

theorem schedDrivers_regular (c : BoundaryWord) (s : Schedule) {Ω : Type*}
    (h : Ω → DistOn upperHalfPlaneOpens) (j : ℕ) (ω : Ω) :
    IsRegularDriver (schedDrivers h44 hκ hκ4 c s h j ω) :=
  codeDriver_regular h44 hκ hκ4 c (scheduleSpec s) j (h ω)

theorem context_schedDrivers (c : BoundaryWord) (s : Schedule) {Ω : Type*}
    (h : Ω → DistOn upperHalfPlaneOpens) (k : ℕ) (ω : Ω) :
    context κ c (scheduleSpec s) h (schedDrivers h44 hκ hκ4 c s h) k ω =
      codeContext h44 hκ hκ4 c (scheduleSpec s) k (h ω) :=
  context_eq_codeContext h44 hκ hκ4 c (scheduleSpec s) h _ ω k fun _ _ => rfl

end Defs

section Witness

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → Driver}

/-- **The next marked conditional field from the stage-`k` flow-line clause alone** (PROVE-PROP513's
`stageWitness_succ` with `IsStagedHistory` replaced by measurability, regularity and `StageOK` at `k`). -/
theorem stageWitness_succ_of_stageOK (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (s : Schedule) (hEm : ∀ j, Measurable (E j)) (hr : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    (hok : StageOK κ b J P h (scheduleSpec s) E k)
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
  have hpm := measurable_pastMap (κ := κ) runMeasStatement hb spec (fun j _ => hEm j)
    (fun j _ => hr j) (k + 1) le_rfl
  have h𝒢 : pastSigma κ b J spec E (k + 1) ≤ mΩ := by
    rw [pastSigma_eq_comap]; exact hpm.comap_le
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
    runMeasStatement hκ hb hh (fun j _ => hEm j) (fun j _ => hr j) hok
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

end Witness

section Stage

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Stage `k` of the canonical schedule drivers is a conditional flow line** (Astra follow-up 5 §2.1, forward):
given the marked conditional field `(β, Y)` before stage `k` with `(β, Y) = codeContext k (h)` almost surely, for
`P`-a.e. `ω₀` at which stage `k` launches, under `condExpKernel P (pastSigma k) ω₀` the field read in the stage chart
is a GFF with the extreme-height word `β ω₀`, the stage driver is almost surely `stageDriver θ_k (β ω₀, ·)` of it, and
hence its flow-line driver (`isFlowLineDriver_stageDriver`). Also: the stage's lifetime is almost surely infinite. -/
theorem stageOK_schedDrivers (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule) {k : ℕ}
    (hk : k < (scheduleSpec s).2.2.length) {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hw : IsStageWitness κ c.fn c.jumps P h (scheduleSpec s) (schedDrivers h44 hκ hκ4 c s h) k β Y)
    (he : ∀ᵐ ω ∂P, (β ω, Y ω) = codeContext h44 hκ hκ4 c (scheduleSpec s) k (h ω)) :
    StageOK κ c.fn c.jumps P h (scheduleSpec s) (schedDrivers h44 hκ hκ4 c s h) k ∧
      ∀ᵐ ω ∂P, (ExplState.run κ c.fn c.jumps (scheduleSpec s)
          (fun j => schedDrivers h44 hκ hκ4 c s h j ω) (k + 1)).2.2.2.1 k ≠ none →
        (schedDrivers h44 hκ hκ4 c s h k ω).2 = ⊤ := by
  set spec := scheduleSpec s with hspec
  set E := schedDrivers h44 hκ hκ4 c s h with hEdef
  have hb := c.isPiecewiseConstantBoundaryData
  have hB := runMeasStatement.{u}
  have hEm : ∀ j, Measurable (E j) := measurable_schedDrivers h44 hκ hκ4 c s hh.1
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := schedDrivers_regular h44 hκ hκ4 c s h
  have hEm' : ∀ j < k, Measurable (E j) := fun j _ => hEm j
  have hreg' : ∀ j < k, ∀ ω, IsRegularDriver (E j ω) := fun j _ => hreg j
  have hpm : Measurable (pastMap κ c.fn c.jumps spec E k) :=
    measurable_pastMap hB hb spec hEm' hreg' k le_rfl
  have h𝒢 : pastSigma κ c.fn c.jumps spec E k ≤ mΩ := by
    rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hLm : MeasurableSet {ω | (ExplState.run κ c.fn c.jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
    measurableSet_launch_self hB hb hEm' hreg'
  have hL𝒢 : MeasurableSet[pastSigma κ c.fn c.jumps spec E k]
      {ω | (ExplState.run κ c.fn c.jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
    measurableSet_pastSigma_of_run hB hb spec hEm' hreg' hLm fun ω ω' he hω => by
      change (ExplState.run κ c.fn c.jumps spec (fun j => E j ω') (k + 1)).2.2.2.1 k ≠ none
      rw [← launches_run_succ_of_run_eq spec he]
      exact hω
  have hβf : β.FactorsThrough (pastMap κ c.fn c.jumps spec E k) := by
    have hβ := hw.1
    rw [pastSigma_eq_comap] at hβ
    exact hβ.factorsThrough
  have hH : ∀ᵐ ω ∂P, ExtremeHeights κ (β ω) := by
    filter_upwards [he] with ω hω
    have ht := extremeHeights_context hκ hκ4 hc s h E k hk.le ω
    rw [context_schedDrivers, ← hω] at ht
    exact ht
  have hθ := instrAngle_extreme s hk
  -- the kernel statement at almost every launching `ω₀`
  have hK : ∀ᵐ ω₀ ∂P, (ExplState.run κ c.fn c.jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      ∃ h' : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport (ExplState.run κ c.fn c.jumps spec (fun j => E j ω₀) k).2.2.2.2.1 1 0
          (chiC κ) (h ω) (h' ω)) ∧
        (∀ᵐ ω ∂(condExpKernel P (pastSigma κ c.fn c.jumps spec E k) ω₀), (E k ω).2 = ⊤) ∧
        IsFlowLineDriver κ (β ω₀).fn (β ω₀).jumps (instrAngle spec k)
          (condExpKernel P (pastSigma κ c.fn c.jumps spec E k) ω₀) h'
          (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) := by
    filter_upwards [hw.2.2.2, hw.2.2.1, hH, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hw.2.2.1,
      Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 he, ae_ae_run_eq hB hb spec hEm' hreg' (P := P)]
      with ω₀ hk₀ hp₀ hH₀ hpK heK hrunK hl
    obtain ⟨hconf, hlift, -⟩ := hp₀ hl
    set c₀ := (ExplState.run κ c.fn c.jumps spec (fun j => E j ω₀) k).2.2.2.2.1 with hc₀
    set h' : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω)
      with hh'def
    have hT' : ∀ ω, IsChartTransport c₀ 1 0 (chiC κ) (h ω) (h' ω) := fun ω =>
      Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ _
    have hh'm : Measurable h' := (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
    have hYh' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ c.fn c.jumps spec E k) ω₀), Y ω = h' ω := by
      filter_upwards [hpK, hrunK] with ω hpω hrω
      have hlω : (ExplState.run κ c.fn c.jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
        rw [launches_run_succ_of_run_eq spec hrω]; exact hl
      obtain ⟨-, -, hT⟩ := hpω hlω
      rw [hrω] at hT
      exact IsChartTransport.unique hconf hT (hT' ω)
    have hβK : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ c.fn c.jumps spec E k) ω₀), β ω = β ω₀ := by
      filter_upwards [hrunK] with ω hrω
      refine hβf (a := ω) (b := ω₀) ?_
      funext i
      simp only [pastMap, hrω]
    have hG : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ c.fn c.jumps spec E k) ω₀) h'
        (β ω₀).fn (β ω₀).jumps := isGFFWithBoundaryData_congr_ae (hk₀ hl) hh'm hYh'
    have hEK : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ c.fn c.jumps spec E k) ω₀),
        E k ω = stageDriver h44 hκ hκ4 (instrAngle spec k) (β ω₀, h' ω) := by
      filter_upwards [heK, hYh', hβK] with ω hωe hωY hωβ
      change stageDriver h44 hκ hκ4 (instrAngle spec k) (codeContext h44 hκ hκ4 c spec k (h ω)) = _
      rw [← hωe, hωY, hωβ]
    obtain ⟨htop, hfl⟩ := isFlowLineDriver_stageDriver h44 hκ hκ4 hθ hH₀ hG (hEm k) hEK
    exact ⟨h', hT', htop, hfl⟩
  refine ⟨?_, ?_⟩
  · filter_upwards [hK] with ω₀ hK₀ c' θ hcθ
    obtain ⟨hspec', -, hc'⟩ := eq_launch_of_launches spec _ hcθ
    have hθ' : instrAngle spec k = θ := by unfold instrAngle; rw [hspec']
    obtain ⟨h', hT', -, hfl⟩ := hK₀ (by rw [hcθ]; exact Option.some_ne_none _)
    rw [hc'.symm] at hT'
    rw [hθ'] at hfl
    exact ⟨_, _, h', (β ω₀).isPiecewiseConstantBoundaryData, hT', hfl⟩
  · have hA : MeasurableSet {ω | (E k ω).2 = ⊤} :=
      measurableSet_eq_fun (measurable_snd.comp (hEm k)) measurable_const
    have h1 : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ c.fn c.jumps spec E k) ω₀),
        ω ∈ {ω | (ExplState.run κ c.fn c.jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none}ᶜ ∪
          {ω | (E k ω).2 = ⊤} := by
      filter_upwards [hK, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hL𝒢.compl] with ω₀ hK₀ hc₀
      by_cases hl : (ExplState.run κ c.fn c.jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none
      · obtain ⟨-, -, htop, -⟩ := hK₀ hl
        exact htop.mono fun ω hω => Or.inr hω
      · exact (hc₀ hl).mono fun ω hω => Or.inl hω
    filter_upwards [Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 (hLm.compl.union hA) h1] with ω hω hl
    rcases hω with hω | hω
    · exact absurd hl hω
    · exact hω

/-- **The induction along the schedule**: before every instruction `k ≤ L`, the earlier stages are conditional flow
lines, and the marked conditional field before `k` is the code context of the field, with all earlier lifetimes
infinite almost surely. -/
theorem schedDrivers_induction (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule) :
    ∀ k, k ≤ (scheduleSpec s).2.2.length →
      (∀ j < k, StageOK κ c.fn c.jumps P h (scheduleSpec s) (schedDrivers h44 hκ hκ4 c s h) j) ∧
      ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
        IsStageWitness κ c.fn c.jumps P h (scheduleSpec s) (schedDrivers h44 hκ hκ4 c s h) k β Y ∧
        ∀ᵐ ω ∂P, (β ω, Y ω) = codeContext h44 hκ hκ4 c (scheduleSpec s) k (h ω) ∧
          ∀ j < k, (schedDrivers h44 hκ hκ4 c s h j ω).2 = ⊤ := by
  set E := schedDrivers h44 hκ hκ4 c s h with hEdef
  have hEm : ∀ j, Measurable (E j) := measurable_schedDrivers h44 hκ hκ4 c s hh.1
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := schedDrivers_regular h44 hκ hκ4 c s h
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun _ => c, h, stageWitness_zero s c hh, ?_⟩
    exact Eventually.of_forall fun _ => ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro hk1
    have hk : k < (scheduleSpec s).2.2.length := by omega
    obtain ⟨hok, β, Y, hw, he⟩ := ih hk.le
    obtain ⟨hokk, htopk⟩ := stageOK_schedDrivers h44 hκ hκ4 c hc hh s hk hw (he.mono fun _ hω => hω.1)
    have hTop : ∀ᵐ ω ∂P, ∀ j < k + 1, (E j ω).2 = ⊤ := by
      filter_upwards [he, htopk] with ω hω htω j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hω.2 j hj
      · exact htω (launch_of_previous_top s _ hk hω.2)
    refine ⟨fun j hj => ?_, _, _, stageWitness_succ_of_stageOK hκ c.isPiecewiseConstantBoundaryData hh s
      hEm hreg hokk hk hTop hw, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hok j hj
      · exact hokk
    filter_upwards [he, hTop] with ω hω hTω
    have hctx := hω.1
    have hR : pastMap κ c.fn c.jumps (scheduleSpec s) E (k + 1) ω (Fin.last k) =
        recOf (instrTime (scheduleSpec s) k) (E k ω) :=
      pastMap_last_of_launch (launch_of_previous_top s _ hk fun j hj => hTω j (by omega))
    refine ⟨?_, hTω⟩
    rw [hR]
    change advance κ (instrAngle (scheduleSpec s) k) (instrTime (scheduleSpec s) k)
      (E k ω) (β ω, Y ω) = _
    rw [hctx]
    rfl

/-- Instructions past the end of a schedule launch nothing. -/
theorem stageOK_of_length_le {b : ℝ → ℝ} {J : Finset ℝ} (s : Schedule) {E : ℕ → Ω → Driver} {k : ℕ}
    (hk : (scheduleSpec s).2.2.length ≤ k) : StageOK κ b J P h (scheduleSpec s) E k := by
  refine Eventually.of_forall fun ω₀ c' θ hcθ => ?_
  have h1 := (eq_launch_of_launches (scheduleSpec s) _ hcθ).1
  rw [List.getElem?_eq_none hk] at h1
  exact absurd h1 (by simp)

/-- **The canonical drivers of every fixed extreme-angle schedule are a staged history of the field** (R48-safe). -/
theorem isStagedHistory_schedDrivers (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule) :
    IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (schedDrivers h44 hκ hκ4 c s h) := by
  have hEm := measurable_schedDrivers h44 hκ hκ4 c s hh.1
  have hreg := schedDrivers_regular h44 hκ hκ4 c s h
  refine ⟨hEm, fun k => ?_, fun k => Eventually.of_forall fun ω => (hreg k ω).2.2.2, fun k => ?_⟩
  · rw [pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement c.isPiecewiseConstantBoundaryData (scheduleSpec s)
      (fun j _ => hEm j) (fun j _ => hreg j) k le_rfl).comap_le
  · by_cases hk : k < (scheduleSpec s).2.2.length
    · exact (schedDrivers_induction h44 hκ hκ4 c hc hh s (k + 1) hk).1 k (Nat.lt_succ_self k)
    · exact stageOK_of_length_le s (not_lt.1 hk)

/-- **The R51 regularity of the canonical schedule drivers**: almost surely every launched ordinary piece starts at
`0`, is continuous through its stop, and has a generating trace there (the pieces are simple transient curves). -/
theorem stagedPiecesRegular_schedDrivers (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule) :
    StagedPiecesRegular κ c.fn c.jumps P (scheduleSpec s) (schedDrivers h44 hκ hκ4 c s h) := by
  have hreg := schedDrivers_regular h44 hκ hκ4 c s h
  filter_upwards [ae_schedule_goodPath h44 hκ hκ4 c hc hh s
    (isStagedHistory_schedDrivers h44 hκ hκ4 c hc hh s) hreg] with ω hg k θ t c' hk _
  have hkL : k < (scheduleSpec s).2.2.length := (List.getElem?_eq_some_iff.1 hk).1
  have hgood := hg k hkL
  have htop := (Sec7.StripWall.mem_goodPathSet.1 hgood).1
  have hcont := Sec7.StripWall.continuous_of_isRegularDriver (hreg k ω) htop
  have hgood' : WangWu.ImgDrv.GoodPath (schedDrivers h44 hκ hκ4 c s h k ω).1 ⊤ := by
    simpa only [htop] using (Sec7.StripWall.mem_goodPathSet.1 hgood)
  obtain ⟨η, hη, -, -, -⟩ := Sec7.StripWall.exists_simple_trace_of_goodPath hcont (hreg k ω).2.1 hgood'
  have ht : instrTime (scheduleSpec s) k = t := by simp only [instrTime, hk]
  have htfin : t ≠ ⊤ := ht ▸ instrTime_finite s hkL
  rw [htop, min_eq_left le_top]
  exact ⟨(hreg k ω).2.1, hcont.continuousOn, η, hη.mono_horizon le_top, fun h => absurd h htfin⟩

end Stage

/-- **Input (B) of Proposition 5.13, for every field with extreme-height data**: one family of staged histories,
indexed by all fixed extreme-angle schedules, of the field on its own space, with the R51 regularity and drivers
regular at every sample. R48-safe: only `Theorem12ParamCond44Statement` (R74) is used. -/
theorem exists_schedule_stagedHistories (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) :
    ∃ E : Schedule → ℕ → Ω → Driver,
      (∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (E s)) ∧
      (∀ s, StagedPiecesRegular κ c.fn c.jumps P (scheduleSpec s) (E s)) ∧
      (∀ s j ω, IsRegularDriver (E s j ω)) ∧
      ∀ s j ω, E s j ω = codeDriver h44 hκ hκ4 c (scheduleSpec s) j (h ω) :=
  ⟨fun s => schedDrivers h44 hκ hκ4 c s h, fun s => isStagedHistory_schedDrivers h44 hκ hκ4 c hc hh s,
    fun s => stagedPiecesRegular_schedDrivers h44 hκ hκ4 c hc hh s,
    fun s => schedDrivers_regular h44 hκ hκ4 c s h, fun _ _ _ => rfl⟩

end InteractingSLE.Sec5.Prop59Sched
