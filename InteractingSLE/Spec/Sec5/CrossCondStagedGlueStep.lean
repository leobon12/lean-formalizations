/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedGlueDet
import InteractingSLE.Spec.Restart.StagedEntranceStrip

/-!
# One restart step of an extreme-angle schedule: the launch, the chart and the conditional determination (R48-safe)

Packet PROVE-STAGED5. PROVE-STAGEDLOC2's staged restart
(`Restart.StagedEntrance.Staged.isEntranceHistoryLocal_frozenPath_staged`, R48-safe form
`isEntranceHistoryLocal_staged_of_pathRecords_schedule`) adds one piece to an entrance-history local path.
Besides the deterministic path facts (record reconstructions, the concatenation formula and the frontier of the chart
domain), it asks for the launch of the piece in a chart `c` that is conformal **at every sample**, and for the
determination of the piece's chart trace by the field read in `c`, **under the regular conditional law** given the past
path. For the pieces of an extreme-angle schedule these are proved here from the §4.2 codes:

* `runChart`, `ctxWord`: the chart of the state before instruction `k`, and the stage word read off the retained past
  (`stopWord` iterated on the records); **`context_fst_eq_ctxWord`**: at launches the word of the code context is
  `ctxWord` of the retained past;
* **`ae_launch_schedule`**: almost surely every instruction of the schedule launches its piece in the state's chart at
  the instruction's angle;
* **`ae_stage_chart_schedule`**: almost surely the state's chart is conformal with a continuous lift, and the launched
  driver is the stage driver (§4.2 code, direct or reflected) of the stage word and of the field read in that chart;
* **`ae_ae_stage_chart_schedule`**: the same under almost every regular conditional law given the retained past, with
  the word and the chart those of the conditioning sample;
* **`isEntranceHistoryLocal_schedule_step`**: the restart step for instruction `k`, whose remaining hypotheses are the
  deterministic path facts — the record reconstructions `r`, `ψ`, the frontier of the state's chart domain on the old
  path (almost surely), a continuous version `ηc` of the capped chart trace, and the concatenation formula with the
  state's chart (almost surely). The chart is replaced by the identity off a null set, so that it is conformal at every
  sample.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or a `*_of_param` result; the
only named input is `AdmCode.Theorem12ParamCond44Statement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedGlue

open Exist.Staged Exist.StagedLaw Sec7.AdmCode Prop513TreeExtract Prop513Schedule
open Restart (BoundaryWord)
open Restart.StagedEntrance (frozenPath)
open Theorem14.SB.SewGerm (frozenHistory)

/-! ### The state's chart and the stage word read off the retained past -/

section Word

variable {κ : ℝ}

/-- The chart of the state of a schedule before instruction `k` (the launch chart of the piece of instruction `k`). -/
def runChart (κ : ℝ) (c₀ : BoundaryWord) (s : Schedule) {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (ω : Ω) : Chart :=
  (ExplState.run κ c₀.fn c₀.jumps (scheduleSpec s) (fun j => E j ω) k).2.2.2.2.1

/-- The stage word before instruction `k`, read off the retained past: the stop word iterated on the records. -/
def ctxWord (κ : ℝ) (c₀ : BoundaryWord) (spec : ExplSpec) : (k : ℕ) → PastData k → BoundaryWord
  | 0, _ => c₀
  | k + 1, u => stopWord κ (ctxWord κ c₀ spec k (Fin.init (α := fun _ => RecData) u), instrAngle spec k,
      u (Fin.last k))

theorem measurable_ctxWord (κ : ℝ) (c₀ : BoundaryWord) (spec : ExplSpec) :
    ∀ k, Measurable (ctxWord κ c₀ spec k)
  | 0 => measurable_const
  | k + 1 => by
    have hinit : Measurable fun u : PastData (k + 1) => Fin.init (α := fun _ => RecData) u :=
      measurable_pi_iff.2 fun i => measurable_pi_apply _
    exact (measurable_stopWord κ).comp (((measurable_ctxWord κ c₀ spec k).comp hinit).prodMk
      (measurable_const.prodMk (measurable_pi_apply _)))

/-- **At launches, the word of the code context is the stage word of the retained past.** -/
theorem context_fst_eq_ctxWord (c₀ : BoundaryWord) (spec : ExplSpec) {Ω : Type*}
    (h : Ω → DistOn upperHalfPlaneOpens) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    ∀ k, (∀ j < k, (ExplState.run κ c₀.fn c₀.jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j ≠ none) →
      (context κ c₀ spec h E k ω).1 = ctxWord κ c₀ spec k (pastMap κ c₀.fn c₀.jumps spec E k ω)
  | 0, _ => rfl
  | k + 1, hl => by
    have ih := context_fst_eq_ctxWord c₀ spec h E ω k fun j hj => hl j (Nat.lt_succ_of_lt hj)
    have hinit : Fin.init (α := fun _ => RecData) (pastMap κ c₀.fn c₀.jumps spec E (k + 1) ω) =
        pastMap κ c₀.fn c₀.jumps spec E k ω := by
      rw [pastMap_succ, Fin.init_snoc]
    change stopWord κ ((context κ c₀ spec h E k ω).1, instrAngle spec k, recOf (instrTime spec k) (E k ω)) =
      stopWord κ (ctxWord κ c₀ spec k (Fin.init (α := fun _ => RecData)
        (pastMap κ c₀.fn c₀.jumps spec E (k + 1) ω)), instrAngle spec k,
        pastMap κ c₀.fn c₀.jumps spec E (k + 1) ω (Fin.last k))
    rw [ih, hinit, pastMap_last_of_launch (hl k (Nat.lt_succ_self k))]

end Word

/-! ### The launch and the stage driver -/

section Stage

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

include h44 hκ hκ4

/-- **Almost surely every instruction of an extreme-angle schedule launches its piece**, in the state's chart and at
the instruction's angle. -/
theorem ae_launch_schedule (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, ∀ k < (scheduleSpec s).2.2.length,
      (ExplState.run κ c₀.fn c₀.jumps (scheduleSpec s) (fun j => E j ω) (k + 1)).2.2.2.1 k =
        some (runChart κ c₀ s E k ω, instrAngle (scheduleSpec s) k) := by
  filter_upwards [ae_schedule_drivers h44 hκ hκ4 c₀ hc₀ hh s hE hreg] with ω hω k hk
  have hl : (ExplState.run κ c₀.fn c₀.jumps (scheduleSpec s) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none :=
    launch_of_previous_top s (fun j => E j ω) hk fun j hj => (hω j (hj.trans hk)).1
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨-, -, hc⟩ := eq_launch_of_launches _ _ hcθ
  have hθ := angle_of_launch _ _ hcθ
  rw [hcθ, hc, hθ]
  rfl

/-- **The launched driver is the stage driver of the stage word and of the field read in the state's chart**
(almost surely; the chart is conformal with a continuous lift). -/
theorem ae_stage_chart_schedule (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {k : ℕ} (hk : k < (scheduleSpec s).2.2.length) :
    ∀ᵐ ω ∂P, (runChart κ c₀ s E k ω).IsConformal ∧
      ContinuousOn (fun w => (runChart κ c₀ s E k ω).2.2 ((runChart κ c₀ s E k ω).2.1 w)) H ∧
      ∀ (c' : Chart) (hc' : c'.IsConformal), c' = runChart κ c₀ s E k ω →
        E k ω = stageDriver h44 hκ hκ4 (instrAngle (scheduleSpec s) k)
          (ctxWord κ c₀ (scheduleSpec s) k (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k ω),
            Chart.chartTransport hc' 1 0 (chiC κ) (h ω)) := by
  obtain ⟨β, Y, hw, he⟩ := finite_schedule_induction h44 hκ hκ4 c₀ hc₀ hh s hE hreg k hk.le
  filter_upwards [hw.2.2.1, he, ae_schedule_drivers h44 hκ hκ4 c₀ hc₀ hh s hE hreg] with ω hp hctx hd
  obtain ⟨hctx, hprev⟩ := hctx
  have hl : (ExplState.run κ c₀.fn c₀.jumps (scheduleSpec s) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none :=
    launch_of_previous_top s (fun j => E j ω) hk fun j hj => (hprev j hj).1
  obtain ⟨hconf, hlift, hT⟩ := hp hl
  refine ⟨hconf, hlift, fun c' hc' hcc => ?_⟩
  subst hcc
  have hY : Y ω = Chart.chartTransport hc' 1 0 (chiC κ) (h ω) :=
    hT.eq_chartTransport hc' (Chart.locallyIntegrableOn_of_continuousOn hlift)
  have hcE : context κ c₀ (scheduleSpec s) h E k ω = codeContext h44 hκ hκ4 c₀ (scheduleSpec s) k (h ω) :=
    context_eq_codeContext h44 hκ hκ4 c₀ (scheduleSpec s) h E ω k fun j hj => (hprev j hj).2
  have hlj : ∀ j < k, (ExplState.run κ c₀.fn c₀.jumps (scheduleSpec s) (fun i => E i ω) (j + 1)).2.2.2.1 j ≠
      none := fun j hj => launch_of_previous_top s (fun i => E i ω) (hj.trans hk) fun i hi =>
        (hprev i (hi.trans hj)).1
  have hword := context_fst_eq_ctxWord (κ := κ) c₀ (scheduleSpec s) h E ω k hlj
  rw [(hd k hk).2]
  change stageDriver h44 hκ hκ4 (instrAngle (scheduleSpec s) k)
    (codeContext h44 hκ hκ4 c₀ (scheduleSpec s) k (h ω)) = _
  rw [← hcE]
  congr 1
  refine Prod.ext hword ?_
  rw [hcE, ← hctx]
  exact hY

/-- **Under almost every regular conditional law given the retained past, the launched driver is the stage driver of
the conditioning sample's word and of the field read in the conditioning sample's chart.** -/
theorem ae_ae_stage_chart_schedule (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {k : ℕ} (hk : k < (scheduleSpec s).2.2.length) :
    ∀ᵐ ω₀ ∂P, ∀ (c' : Chart) (hc' : c'.IsConformal), c' = runChart κ c₀ s E k ω₀ →
      ∀ᵐ ω ∂(condExpKernel P (_root_.InteractingSLE.pastSigma κ c₀.fn c₀.jumps (scheduleSpec s) E k) ω₀),
        E k ω = stageDriver h44 hκ hκ4 (instrAngle (scheduleSpec s) k)
          (ctxWord κ c₀ (scheduleSpec s) k (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k ω₀),
            Chart.chartTransport hc' 1 0 (chiC κ) (h ω)) := by
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae (hE.2.1 k)
      (ae_stage_chart_schedule h44 hκ hκ4 c₀ hc₀ hh s hE hreg hk),
    ae_ae_run_eq runMeasStatement c₀.isPiecewiseConstantBoundaryData (scheduleSpec s) (k := k)
      (fun j _ => hE.1 j) (fun j _ => hreg j) (P := P)] with ω₀ h1 h2 c' hc' hcc
  filter_upwards [h1, h2] with ω hω hr
  have hchart : runChart κ c₀ s E k ω = runChart κ c₀ s E k ω₀ := by
    unfold runChart
    rw [hr]
  have hpast : pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k ω =
      pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k ω₀ := by
    unfold pastMap
    rw [hr]
  rw [← hpast]
  exact hω.2.2 c' hc' (hcc.trans hchart.symm)

end Stage

/-! ### The restart step -/

section Step

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

include h44 hκ hκ4

/-- **The restart step for the piece of instruction `k` of an extreme-angle schedule** (R48-safe). Let `α` be a
continuous path from `x ∉ ℍ` (measurable at fixed times) whose stopped path at the rational time `q₀` is
entrance-history local for the centred field and reconstructs, and is reconstructed from, the retained past before
`k` (Borel maps `r`, `ψ`). Suppose that almost surely the frontier in `ℍ` of the state's chart domain lies on
`α([0, q₀])`, and that `ηc` is a continuous version (from `0`, measurable at fixed times) of the piece's chart
trace `β` capped at own time `m`, with `α(q₀ + u) = c⁻¹(ηc(u))`, `ηc(u) ∈ ℍ` for `u > 0` (`c` the state's chart).
Then `α` frozen at `q₀ + m` is entrance-history local for the centred field. The launch, the chart's conformality
and lift, and the conditional determination of `ηc` by the field read in the chart are proved
(`ae_launch_schedule`, `ae_stage_chart_schedule`, `ae_ae_stage_chart_schedule`). -/
theorem isEntranceHistoryLocal_schedule_step (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c₀.fn c₀.jumps u₀) {k : ℕ}
    (hk : k < (scheduleSpec s).2.2.length)
    {α : Ω → ℝ≥0 → ℂ} {x : ℂ} (hxH : x ∉ H) (hαc : ∀ ω, Continuous (α ω))
    (hα0 : ∀ ω, α ω 0 = x) (hαm : ∀ t, Measurable fun ω => α ω t)
    {q₀ : ℚ≥0} (m : ℝ≥0) {r : ℝ≥0 → PastData k → ℂ} (hrm : ∀ t, Measurable (r t))
    (hrr : ∀ t : ℝ≥0, (fun ω => frozenPath (α ω) q₀ t) =ᵐ[P]
      fun ω => r t (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k ω))
    {ψ : (Fin 1 → Sec6.Hist) → PastData k} (hψ : Measurable ψ)
    (hrec : pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k =ᵐ[P] fun ω => ψ (frozenHistory α q₀ ω))
    (hloc₀ : Sec6.IsEntranceHistoryLocal (fun ω => frozenPath (α ω) q₀) (WholeField.centredField h u₀) P)
    (hfr : ∀ᵐ ω ∂P, ∀ z ∈ H, z ∈ closure ((runChart κ c₀ s E k ω).dom : Set ℂ) →
      z ∉ (runChart κ c₀ s E k ω).dom → z ∈ α ω '' Icc 0 (q₀ : ℝ≥0))
    {β ηc : Ω → ℝ≥0 → ℂ} (hηc : ∀ ω, Continuous (ηc ω))
    (hηm : ∀ t, Measurable fun ω => ηc ω t) (hη0 : ∀ ω, ηc ω 0 = 0)
    (htrβ : ∀ᵐ ω ∂P, IsGeneratingTrace (E k ω).1 (E k ω).2 (β ω))
    (hηβ : ∀ᵐ ω ∂P, ∀ t, ηc ω t = β ω (Restart.capTime m (E k ω).2 t))
    (hcat : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, 0 < v → ηc ω v ∈ H ∧
      frozenPath (α ω) ((q₀ : ℝ≥0) + m) ((q₀ : ℝ≥0) + v) = (runChart κ c₀ s E k ω).2.1 (ηc ω v)) :
    Sec6.IsEntranceHistoryLocal (fun ω => frozenPath (α ω) ((q₀ : ℝ≥0) + m))
      (WholeField.centredField h u₀) P := by
  classical
  have hK := Theorem14.SB.SewGerm.ae_condExpKernel_stage_eq_path hE hαm hrm hrr hψ hrec
  have hC := ae_stage_chart_schedule h44 hκ hκ4 c₀ hc₀ hh s hE hreg hk
  -- the state's chart, replaced by the identity off the good event
  let G : Ω → Prop := fun ω => (runChart κ c₀ s E k ω).IsConformal ∧
    ContinuousOn (fun w => (runChart κ c₀ s E k ω).2.2 ((runChart κ c₀ s E k ω).2.1 w)) H ∧
    ∀ z ∈ H, z ∈ closure ((runChart κ c₀ s E k ω).dom : Set ℂ) →
      z ∉ (runChart κ c₀ s E k ω).dom → z ∈ α ω '' Icc 0 (q₀ : ℝ≥0)
  have hG : ∀ᵐ ω ∂P, G ω := by
    filter_upwards [hC, hfr] with ω h1 h2
    exact ⟨h1.1, h1.2.1, h2⟩
  let c : Ω → Chart := fun ω => if G ω then runChart κ c₀ s E k ω else Chart.id
  have hcG : ∀ ω, G ω → c ω = runChart κ c₀ s E k ω := fun ω hω => by
    simp only [c, hω, ↓reduceIte]
  have hcN : ∀ ω, ¬ G ω → c ω = Chart.id := fun ω hω => by
    simp only [c, hω, ↓reduceIte]
  have hc : ∀ ω, (c ω).IsConformal := fun ω => by
    by_cases hω : G ω
    · rw [hcG ω hω]; exact hω.1
    · rw [hcN ω hω]; exact Chart.isConformal_id
  have hℓ : ∀ ω, LocallyIntegrableOn (fun w => (c ω).2.2 ((c ω).2.1 w)) H := fun ω => by
    apply Chart.locallyIntegrableOn_of_continuousOn
    by_cases hω : G ω
    · rw [hcG ω hω]; exact hω.2.1
    · rw [hcN ω hω]; exact Chart.continuousOn_id_lift
  have hfr' : ∀ ω, ∀ z ∈ H, z ∈ closure ((c ω).dom : Set ℂ) → z ∉ (c ω).dom →
      z ∈ α ω '' Icc 0 (q₀ : ℝ≥0) := by
    intro ω z hz hcl hnd
    by_cases hω : G ω
    · rw [hcG ω hω] at hcl hnd
      exact hω.2.2 z hz hcl hnd
    · rw [hcN ω hω] at hnd
      exact absurd (Restart.StagedEntrance.Strip.mem_dom_id hz) hnd
  have hlaunch : ∀ᵐ ω ∂P, (ExplState.run κ c₀.fn c₀.jumps (scheduleSpec s) (fun j => E j ω) (k + 1)).2.2.2.1 k =
      some (c ω, instrAngle (scheduleSpec s) k) := by
    filter_upwards [ae_launch_schedule h44 hκ hκ4 c₀ hc₀ hh s hE hreg, hG] with ω hl hω
    rw [hcG ω hω]
    exact hl k hk
  have hcat' : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, 0 < v → ηc ω v ∈ H ∧
      frozenPath (α ω) ((q₀ : ℝ≥0) + m) ((q₀ : ℝ≥0) + v) = (c ω).2.1 (ηc ω v) := by
    filter_upwards [hcat, hG] with ω h1 hω
    rw [hcG ω hω]
    exact h1
  -- the conditional determination of the capped chart trace
  have hpast : Restart.StagedEntrance.pastSigma α (q₀ : ℝ≥0) ≤ mΩ := Restart.StagedEntrance.pastSigma_le hαm
  have hZ : ∀ᵐ ω ∂P, (E k ω).2 = ⊤ :=
    (ae_schedule_drivers h44 hκ hκ4 c₀ hc₀ hh s hE hreg).mono fun ω hω => (hω k hk).1
  have hT1 := KernelTower.ae_ae_condExpKernel_of_ae hpast htrβ
  have hT2 := KernelTower.ae_ae_condExpKernel_of_ae hpast hηβ
  have hT3 := KernelTower.ae_ae_condExpKernel_of_ae hpast hZ
  have hdetη : ∀ᵐ ω₀ ∂P, ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => ηc ω t) =ᵐ[condExpKernel P (Restart.StagedEntrance.pastSigma α q₀) ω₀]
        fun ω => f (Chart.chartTransport (hc ω₀) 1 0 (chiC κ) (h ω)) := by
    filter_upwards [ae_ae_stage_chart_schedule h44 hκ hκ4 c₀ hc₀ hh s hE hreg hk, hK, hG, hT1, hT2, hT3]
      with ω₀ hd hK₀ hg h1 h2 h3 t
    have hd' := hd (c ω₀) (hc ω₀) (hcG ω₀ hg)
    rw [hK₀] at hd'
    refine ⟨fun X => LP.traceAt (Restart.capTime m ⊤ t) (stageDriver h44 hκ hκ4 (instrAngle (scheduleSpec s) k)
      (ctxWord κ c₀ (scheduleSpec s) k (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k ω₀), X)).1, ?_, ?_⟩
    · exact (LP.measurable_traceAt _).comp (measurable_fst.comp
        ((measurable_stageDriver h44 hκ hκ4 _).comp (measurable_const.prodMk measurable_id)))
    · filter_upwards [hd', h1, h2, h3] with ω he hβω hηω hζ
      rw [hηω t, hζ]
      have hcont : Continuous (E k ω).1 := Sec7.StripWall.continuous_of_isRegularDriver (hreg k ω) hζ
      rw [hζ] at hβω
      rw [← LP.traceAt_eq_of_isGeneratingTrace hβω hcont.continuousOn (hreg k ω).2.1 ENNReal.coe_lt_top, he]
  exact isEntranceHistoryLocal_staged_of_pathRecords_schedule h44 hκ hκ4 c₀ hc₀ hh s hE hreg hu₀ k
    (instrAngle (scheduleSpec s) k) hxH hαc hα0 hαm m hrm hrr hψ hrec hloc₀ hc hℓ hlaunch hfr' hηc hηm hη0
    htrβ hηβ hdetη hcat'

end Step

end InteractingSLE.Sec5.CrossCond.StagedGlue
