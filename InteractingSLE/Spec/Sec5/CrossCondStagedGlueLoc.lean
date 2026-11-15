/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedGlueChain

/-!
# The staged prefix of an extreme-angle schedule is a marked local set (R48-safe)

Packet PROVE-STAGED5 (PROVE-CROSSCOND-STAGED4 §5.1, the gate of S2 on the glued space). For the staged history `E` of an
extreme-angle schedule `s` of a GFF `h` whose root word has the extreme heights:

* `recDrvOf`, `recPath`, `pastOfPath`: the two Borel record reconstructions (the frozen joined trace from the retained
  past, through the measurable trace evaluation of the joined record driver; the retained past from the stopped path
  history, through the driver read off the path, `Sec7.StripMark.histDriver`); **`IsGoodSched.frozenPath_eq_recPath`**,
  **`IsGoodSched.pastMap_eq_pastOfPath`**: they are correct on the good event;
* **`exists_isEntranceHistoryLocal_schedule`**: there is a version `α` of the joined trace (continuous at every sample,
  from `0`, measurable at fixed times, almost surely a generating trace of the joined driver on `[0, ∞)`) such that
  `α` frozen at the start time of every piece `n ≤ L` is entrance-history local for the centred field — the induction
  over the pieces with `isEntranceHistoryLocal_schedule_step` (Lemma 6.2's restart, PROVE-STAGEDLOC2), all of whose path
  hypotheses are discharged here (record reconstructions, frontier, join formula, piece versions);
* **`isHistoryAvoidanceLocal_range_of_path_schedule`** (the path route without the identification with `stageSet`) and
  **`exists_isHistoryAvoidanceLocal_schedule`**: the explored set `α([0, S_n]) ∩ ℍ` after `n ≥ 1` pieces is
  history-avoidance local for the retained past `pastSigma n` (the input `hAloc` of the staged glued law, for the
  trace set).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or a `*_of_param` result; the
only named input is `AdmCode.Theorem12ParamCond44Statement` (the approved restricted §4.2 input).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedGlue

open Exist.Staged Exist.StagedLaw Sec7.AdmCode Prop513TreeExtract Prop513Schedule
open Theorem14.GW2Schedule (schedDelta schedDelta_ne_top isFlowProg_scheduleProgram pastMap_of_allSucc)
open Restart (BoundaryWord)
open Restart.StagedEntrance (frozenPath)
open Theorem14.SB.SewGerm (frozenHistory)
open InteractingSLE.Sec5.CrossCond.Staged (catN cumT continuous_catN catN_zero)
open InteractingSLE.Sec5.CrossCond.StagedFinal (startN startN_succ startN_mono catN_add_start)

/-! ### The two record reconstructions -/

section Rec

/-- The record driver of piece `j` read off a retained past `u` (`0` past `k`). -/
def recDrvOf {k : ℕ} (u : PastData k) (j : ℕ) : ℝ≥0 → ℝ :=
  if hj : j < k then Sec7.StripSideHeightProb.recW (u ⟨j, hj⟩) else fun _ => 0

theorem measurable_recDrvOf (k j : ℕ) : Measurable fun u : PastData k => recDrvOf u j := by
  unfold recDrvOf
  split_ifs with hj
  · exact Restart.StagedEntrance.Strip.measurable_recW.comp (measurable_pi_apply _)
  · exact measurable_const

/-- **The frozen joined trace read off the retained past before piece `k + 1`**: the measurable trace evaluation of the
joined record driver. -/
def recPath (s : Schedule) (k : ℕ) (t : ℝ≥0) (u : PastData (k + 1)) : ℂ :=
  LP.traceAt (min t (startN (schedD s) (k + 1))) (catN (recDrvOf u) (schedD s) k)

theorem measurable_recPath (s : Schedule) (k : ℕ) (t : ℝ≥0) : Measurable (recPath s k t) :=
  (LP.measurable_traceAt _).comp (measurable_catN_family (fun j => measurable_recDrvOf (k + 1) j) _ k)

/-- **The retained past before piece `k + 1` read off the stopped joined path history**: record `i` is the increment of
the driver read off the path (`Sec7.StripMark.histDriver`) on the own interval of piece `i`. -/
def pastOfPath (s : Schedule) (k : ℕ) (y : Fin 1 → Sec6.Hist) : PastData (k + 1) := fun i =>
  ((fun q : ℚ => Sec7.StripMark.histDriver (startN (schedD s) (k + 1)) (y 0)
      (startN (schedD s) i + min (q : ℝ).toNNReal (schedD s i)) -
    Sec7.StripMark.histDriver (startN (schedD s) (k + 1)) (y 0) (startN (schedD s) i)),
    ((schedD s i : ℝ≥0) : ℝ≥0∞), false)

theorem measurable_pastOfPath (s : Schedule) (k : ℕ) : Measurable (pastOfPath s k) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hD : Measurable fun y : Fin 1 → Sec6.Hist =>
      Sec7.StripMark.histDriver (startN (schedD s) (k + 1)) (y 0) :=
    (Sec7.StripMark.measurable_histDriver _).comp (measurable_pi_apply 0)
  refine Measurable.prodMk (measurable_pi_iff.2 fun q => ?_) measurable_const
  exact ((measurable_pi_apply _).comp hD).sub ((measurable_pi_apply _).comp hD)

variable {κ : ℝ} {c₀ : BoundaryWord} {s : Schedule} {Ω : Type*} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}

/-- On the good event the retained past is the family of records of the pieces at their own times. -/
theorem IsGoodSched.pastMap_eq (hg : IsGoodSched s E ω) {k : ℕ} (hk : k ≤ schedL s) :
    pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k ω = fun i : Fin k => recOf (schedD s i : ℝ≥0∞) (E i ω) := by
  rw [pastMap_of_allSucc (spec := scheduleSpec s) (κ := κ) (b := c₀.fn) (jumps := c₀.jumps) rfl
    (isFlowProg_scheduleProgram 0 (scheduleList s)) (schedDelta_ne_top 0 _) E hk (hg.allSucc k hk)]
  funext i
  rw [schedD, ENNReal.coe_toNNReal (schedDelta_ne_top _ _ _)]

theorem IsGoodSched.recDrvOf_eq (hg : IsGoodSched s E ω) (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    (hk : k ≤ schedL s) {j : ℕ} (hj : j < k) (r : ℝ≥0) :
    recDrvOf (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k ω) j r = (E j ω).1 (min r (schedD s j)) := by
  have hlt : ((schedD s j : ℝ≥0) : ℝ≥0∞) < (E j ω).2 := by
    rw [(hg j (by omega)).1]
    exact ENNReal.coe_lt_top
  simp only [recDrvOf, hj, ↓reduceDIte]
  rw [hg.pastMap_eq hk]
  exact Sec7.StripMark.recW_recOf_of_lt (hreg j ω) hlt (Sec7.StripMark.isDrvGood_recOf_of_lt (hreg j ω) hlt) r

/-- **The frozen joined trace is reconstructed from the retained past** (on the good event). -/
theorem IsGoodSched.frozenPath_eq_recPath (hg : IsGoodSched s E ω) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (joinW s E ω) ⊤ α) {k : ℕ} (hk : k + 1 ≤ schedL s) (t : ℝ≥0) :
    frozenPath α (startN (schedD s) (k + 1)) t =
      recPath s k t (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (k + 1) ω) := by
  change α (min t (startN (schedD s) (k + 1))) = _
  rw [← LP.traceAt_eq_of_isGeneratingTrace hα hg.continuous_joinW.continuousOn hg.joinW_zero ENNReal.coe_lt_top]
  unfold recPath
  refine LP.traceAt_congr fun r hr => ?_
  have hr' : r ≤ cumT (schedD s) k := hr.trans (min_le_right _ _)
  rw [joinW, catN_of_le_cumT (by omega : k ≤ schedL s - 1) hr']
  refine catN_congr_cumT (fun j hj r' hr'' => ?_) r hr'
  rw [pieceW_of_lt s E ω (by omega), hg.recDrvOf_eq hreg hk (by omega), min_eq_left hr'']

/-- **The retained past is reconstructed from the stopped joined path history** (on the good event). -/
theorem IsGoodSched.pastMap_eq_pastOfPath (hg : IsGoodSched s E ω) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (joinW s E ω) ⊤ α) {k : ℕ} (hk : k + 1 ≤ schedL s) :
    pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (k + 1) ω =
      pastOfPath s k (fun _ => Sec6.histOf (Sec6.pathCoord (frozenPath α (startN (schedD s) (k + 1))))
        ((startN (schedD s) (k + 1) : ℝ≥0) : ℝ≥0∞)) := by
  rw [hg.pastMap_eq hk]
  funext i
  have hiL : (i : ℕ) < schedL s := by omega
  have hlt : ((schedD s i : ℝ≥0) : ℝ≥0∞) < (E i ω).2 := by
    rw [(hg i hiL).1]
    exact ENNReal.coe_lt_top
  rw [Sec7.StripMark.recOf_of_lt hlt]
  unfold pastOfPath
  rw [Restart.StagedEntrance.Strip.histOf_pathCoord_frozenPath]
  refine Prod.ext (funext fun q => ?_) rfl
  have hS : 0 < startN (schedD s) (k + 1) := by
    rw [startN_succ]
    exact add_pos_of_nonneg_of_pos zero_le (schedD_pos s (by omega))
  have hD : ∀ r ≤ startN (schedD s) (k + 1), Sec7.StripMark.histDriver (startN (schedD s) (k + 1))
      (Sec6.histOf (Sec6.pathCoord α) ((startN (schedD s) (k + 1) : ℝ≥0) : ℝ≥0∞)) r = joinW s E ω r :=
    fun r hr => Sec7.StripMark.histDriver_eq hg.continuous_joinW hg.joinW_zero hS
      (IsGeneratingTrace.mono_horizon hα le_top) hr
  have hSi : startN (schedD s) i + schedD s i ≤ startN (schedD s) (k + 1) := by
    rw [← startN_succ]
    exact startN_mono _ (by omega)
  have hmin : min (q : ℝ).toNNReal (schedD s i) ≤ schedD s i := min_le_right _ _
  have h1 : startN (schedD s) i + min (q : ℝ).toNNReal (schedD s i) ≤ cumT (schedD s) k :=
    le_trans (add_le_add le_rfl hmin) hSi
  have h2 : startN (schedD s) i ≤ cumT (schedD s) k := le_trans le_self_add hSi
  dsimp only
  rw [hD _ h1, hD _ h2, joinW, catN_of_le_cumT (by omega : k ≤ schedL s - 1) h1,
    catN_of_le_cumT (by omega : k ≤ schedL s - 1) h2,
    catN_add_start (fun j => (hg.pieceW_cont j).2) k i (by omega) _ hmin, pieceW_of_lt s E ω hiL]
  ring

end Rec

/-! ### The path route for the explored set -/

section Range

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

include h44 hκ hκ4

/-- **The explored set of a continuous retained path is a marked local set for the retained past** (the path route,
R48-safe for extreme-angle schedules; `isHistoryAvoidanceLocal_stage_of_path_schedule` without the identification of
the explored set with `WalkLaw.stageSet`). -/
theorem isHistoryAvoidanceLocal_range_of_path_schedule (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) E) (hr : ∀ j ω, IsRegularDriver (E j ω))
    (u₀ : ℂ → ℝ) {k : ℕ} {α : Ω → ℝ≥0 → ℂ} {T : ℝ≥0} {r : ℝ≥0 → PastData k → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) {x : ℂ} (hα0 : ∀ ω, α ω 0 = x)
    (hαm : ∀ t, Measurable fun ω => α ω t) (hrm : ∀ t, Measurable (r t))
    (hrr : ∀ t : ℝ≥0, (fun ω => frozenPath (α ω) T t) =ᵐ[P]
      fun ω => r t (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k ω))
    {ψ : (Fin 1 → Sec6.Hist) → PastData k} (hψ : Measurable ψ)
    (hrec : pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E k =ᵐ[P] fun ω => ψ (frozenHistory α T ω))
    (hentr : Sec6.IsEntranceHistoryLocal (fun ω => frozenPath (α ω) T) (WholeField.centredField h u₀) P) :
    WholeField.IsHistoryAvoidanceLocal (_root_.InteractingSLE.pastSigma κ c₀.fn c₀.jumps (scheduleSpec s) E k)
      (fun ω => α ω '' Icc 0 T ∩ H) (WholeField.centredField h u₀) P := by
  have hdet := frozenPath_determined_of_schedule h44 hκ hκ4 c₀ hc₀ hh s hE hr u₀ hrm hrr
  have hp := Sec6.isHistoryAvoidanceLocal_explored
    (η := fun _ : Fin 1 => fun ω => frozenPath (α ω) T) (x := fun _ => x)
    (τ := fun _ _ => (T : ℝ≥0∞)) (S := fun _ _ _ => (T : ℝ≥0∞))
    (WholeField.measurable_centredField hh.1 u₀)
    (fun _ ω => Restart.StagedEntrance.continuous_frozenPath (hαc ω))
    (fun _ ω => by rw [Restart.StagedEntrance.frozenPath_zero]; exact hα0 ω)
    (fun _ t => hαm _) (fun _ => hdet) (fun _ => hentr)
    (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
  rw [show Sec6.explored (fun _ : Fin 1 => fun ω => frozenPath (α ω) T)
    (fun _ _ => (T : ℝ≥0∞)) = fun ω => α ω '' Icc 0 T ∩ H from
      funext Restart.StagedEntrance.explored_frozenPath] at hp
  have hle := KernelTower.comap_le_aeSigma_comap hψ hrec
  exact Sec7.StripMark.isHistoryAvoidanceLocal_of_ae_le hp fun F hF => hle F hF

end Range

/-! ### The induction over the pieces -/

section Main

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

theorem zero_not_mem_H : (0 : ℂ) ∉ H := fun h0 => by
  have h0' : (0 : ℝ) < (0 : ℂ).im := h0
  rw [Complex.zero_im] at h0'
  exact lt_irrefl _ h0'

include h44 hκ hκ4

/-- **One more piece**, with all path hypotheses discharged from given versions: if `α` (a version of the joined
trace) frozen at the start time `S_k` of piece `k < L` is entrance-history local, so is `α` frozen at `S_{k+1}`. The
versions `β` of the piece traces are almost surely generating traces staying in `ℍ`. -/
theorem isEntranceHistoryLocal_schedule_succ (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c₀.fn c₀.jumps u₀)
    {α : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => α ω t) (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (joinW s E ω) ⊤ (α ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβ0 : ∀ ω, β ω 0 = 0) {k : ℕ} (hk : k < schedL s)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E k ω).1 ⊤ (β ω) ∧ ∀ t, 0 < t → β ω t ∈ H)
    (hloc : Sec6.IsEntranceHistoryLocal (fun ω => frozenPath (α ω) (startN (schedD s) k))
      (WholeField.centredField h u₀) P) :
    Sec6.IsEntranceHistoryLocal (fun ω => frozenPath (α ω) (startN (schedD s) (k + 1)))
      (WholeField.centredField h u₀) P := by
  have hG := ae_isGoodSched h44 hκ hκ4 c₀ hc₀ hh s hE hreg
  obtain ⟨q₀, hq₀⟩ := exists_nnrat_startN s k hk.le
  rw [← hq₀] at hloc
  rw [startN_succ, ← hq₀]
  have hd := schedD_pos s hk
  -- the piece-specific hypotheses
  have hfr : ∀ᵐ ω ∂P, ∀ z ∈ H, z ∈ closure ((runChart κ c₀ s E k ω).dom : Set ℂ) →
      z ∉ (runChart κ c₀ s E k ω).dom → z ∈ α ω '' Icc 0 (q₀ : ℝ≥0) := by
    filter_upwards [hG, hαtr] with ω hg hα
    rw [hq₀]
    exact hg.frontier_runChart hα hk.le
  have htrβ : ∀ᵐ ω ∂P, IsGeneratingTrace (E k ω).1 (E k ω).2 (β ω) := by
    filter_upwards [hG, hβtr] with ω hg hb
    rw [(hg k hk).1]
    exact hb.1
  have hηβ : ∀ᵐ ω ∂P, ∀ t, β ω (min t (schedD s k)) = β ω (Restart.capTime (schedD s k) (E k ω).2 t) := by
    filter_upwards [hG] with ω hg t
    rw [Restart.capTime, (hg k hk).1, min_top_left, ENNReal.toNNReal_coe]
  have hcat : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, 0 < v → β ω (min v (schedD s k)) ∈ H ∧
      frozenPath (α ω) ((q₀ : ℝ≥0) + schedD s k) ((q₀ : ℝ≥0) + v) =
        (runChart κ c₀ s E k ω).2.1 (β ω (min v (schedD s k))) := by
    filter_upwards [hG, hαtr, hβtr] with ω hg hα hb v hv
    have hu : 0 < min v (schedD s k) := lt_min hv hd
    refine ⟨hb.2 _ hu, ?_⟩
    change α ω (min ((q₀ : ℝ≥0) + v) ((q₀ : ℝ≥0) + schedD s k)) = _
    rw [min_add_add_left, hq₀]
    exact hg.join_runChart hα hk hb.1 hb.2 hu (min_le_right _ _)
  have hηc : ∀ ω, Continuous fun v => β ω (min v (schedD s k)) := fun ω =>
    (hβc ω).comp (continuous_id.min continuous_const)
  have hηm : ∀ t, Measurable fun ω => β ω (min t (schedD s k)) := fun t => hβm _
  have hη0 : ∀ ω, β ω (min 0 (schedD s k)) = 0 := fun ω => by rw [min_eq_left zero_le]; exact hβ0 ω
  cases k with
  | zero =>
    -- the first piece: the old path is the constant `0`, the past is trivial
    have hq0 : (q₀ : ℝ≥0) = 0 := by rw [hq₀]; simp only [startN, Finset.range_zero, Finset.sum_empty]
    refine isEntranceHistoryLocal_schedule_step h44 hκ hκ4 c₀ hc₀ hh s hE hreg hu₀ hk zero_not_mem_H hαc hα0 hαm
      (schedD s 0) (r := fun _ _ => (0 : ℂ)) (fun _ => measurable_const) (fun t => ?_) (ψ := fun _ => fun i => i.elim0)
      measurable_const (Eventually.of_forall fun ω => funext fun i => i.elim0) hloc hfr hηc hηm hη0 htrβ
      (hηβ.mono fun ω hω t => hω t) hcat
    refine Eventually.of_forall fun ω => ?_
    change α ω (min t (q₀ : ℝ≥0)) = 0
    rw [hq0, min_eq_right zero_le]
    exact hα0 ω
  | succ k =>
    refine isEntranceHistoryLocal_schedule_step h44 hκ hκ4 c₀ hc₀ hh s hE hreg hu₀ hk zero_not_mem_H hαc hα0 hαm
      (schedD s (k + 1)) (r := recPath s k) (measurable_recPath s k) (fun t => ?_) (ψ := pastOfPath s k)
      (measurable_pastOfPath s k) ?_ hloc hfr hηc hηm hη0 htrβ (hηβ.mono fun ω hω t => hω t) hcat
    · filter_upwards [hG, hαtr] with ω hg hα
      rw [hq₀]
      exact hg.frozenPath_eq_recPath hreg hα hk.le t
    · filter_upwards [hG, hαtr] with ω hg hα
      change _ = pastOfPath s k (fun _ => Sec6.histOf (Sec6.pathCoord (frozenPath (α ω) (q₀ : ℝ≥0)))
        (((q₀ : ℝ≥0) : ℝ≥0∞)))
      rw [hq₀]
      exact hg.pastMap_eq_pastOfPath hα hk.le

/-- **The joined trace of an extreme-angle schedule is entrance-history local at every start time** (R48-safe). There is
a version `α` of the joined trace (continuous at every sample, from `0`, measurable at fixed times, almost surely a
generating trace of the joined driver on `[0, ∞)`) such that `α` frozen at the start time `S_n` of every `n ≤ L` is
entrance-history local for the centred field. -/
theorem exists_isEntranceHistoryLocal_schedule (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c₀.fn c₀.jumps u₀) :
    ∃ α : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (α ω)) ∧ (∀ ω, α ω 0 = 0) ∧ (∀ t, Measurable fun ω => α ω t) ∧
      (∀ᵐ ω ∂P, IsGeneratingTrace (joinW s E ω) ⊤ (α ω)) ∧
      ∀ n ≤ schedL s, Sec6.IsEntranceHistoryLocal (fun ω => frozenPath (α ω) (startN (schedD s) n))
        (WholeField.centredField h u₀) P := by
  have hG := ae_isGoodSched h44 hκ hκ4 c₀ hc₀ hh s hE hreg
  obtain ⟨α, hαc, hαm, hα0, hαtr⟩ := Restart.StagedPathVersion.exists_continuous_version (P := P)
    (measurable_joinW s hE.1) (hG.mono fun ω hg => ⟨hg.continuous_joinW, hg.joinW_zero, hg.exists_trace_joinW⟩)
  have hβex : ∀ k, ∃ β : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (β ω)) ∧ (∀ t, Measurable fun ω => β ω t) ∧
      (∀ ω, β ω 0 = 0) ∧
      (k < schedL s → ∀ᵐ ω ∂P, IsGeneratingTrace (E k ω).1 ⊤ (β ω) ∧ ∀ t, 0 < t → β ω t ∈ H) := by
    intro k
    by_cases hk : k < schedL s
    · obtain ⟨β, hβc, hβm, hβ0, hβtr⟩ := Restart.StagedPathVersion.exists_continuous_version (P := P)
        (measurable_fst.comp (hE.1 k)) (hG.mono fun ω hg => ⟨(hg k hk).2.1, (hg k hk).2.2.1,
          (hg k hk).2.2.2.elim fun η hη => ⟨η, hη.1⟩⟩)
      refine ⟨β, hβc, hβm, hβ0, fun _ => ?_⟩
      filter_upwards [hβtr, hG] with ω hb hg
      obtain ⟨η, hη, hH⟩ := (hg k hk).2.2.2
      refine ⟨hb.1, fun t ht => ?_⟩
      rw [hb.2 η hη t]
      exact hH t ht
    · exact ⟨fun _ _ => 0, fun _ => continuous_const, fun _ => measurable_const, fun _ => rfl,
        fun h' => absurd h' hk⟩
  choose β hβc hβm hβ0 hβtr using hβex
  have hXm := WholeField.measurable_centredField hh.1 u₀
  refine ⟨α, hαc, hα0, hαm, hαtr.mono fun ω hω => hω.1, fun n => ?_⟩
  induction n with
  | zero =>
    intro _
    have e : startN (schedD s) 0 = 0 := by simp only [startN, Finset.range_zero, Finset.sum_empty]
    rw [e]
    exact Restart.StagedEntrance.Staged.isEntranceHistoryLocal_frozenPath_zero hXm hα0
  | succ k ih =>
    intro hk
    exact isEntranceHistoryLocal_schedule_succ h44 hκ hκ4 c₀ hc₀ hh s hE hreg hu₀ hαc hα0 hαm
      (hαtr.mono fun ω hω => hω.1) (hβc k) (hβm k) (hβ0 k) (by omega) (hβtr k (by omega)) (ih (by omega))

/-- **The explored set of the staged prefix of an extreme-angle schedule is a marked local set for the retained past**
(R48-safe; the gate of PROVE-CROSSCOND-STAGED4 §5.1, for the trace set): with the version `α` of
`exists_isEntranceHistoryLocal_schedule`, for every `n + 1 ≤ L` the set `α([0, S_{n+1}]) ∩ ℍ` (the pieces `0, …, n`) is
history-avoidance local for the centred field and the retained past `pastSigma (n + 1)`. -/
theorem exists_isHistoryAvoidanceLocal_schedule (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c₀.fn c₀.jumps u₀) :
    ∃ α : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (α ω)) ∧ (∀ ω, α ω 0 = 0) ∧ (∀ t, Measurable fun ω => α ω t) ∧
      (∀ᵐ ω ∂P, IsGeneratingTrace (joinW s E ω) ⊤ (α ω)) ∧
      ∀ n, n + 1 ≤ schedL s → WholeField.IsHistoryAvoidanceLocal
        (_root_.InteractingSLE.pastSigma κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1))
        (fun ω => α ω '' Icc 0 (startN (schedD s) (n + 1)) ∩ H) (WholeField.centredField h u₀) P := by
  obtain ⟨α, hαc, hα0, hαm, hαtr, hloc⟩ :=
    exists_isEntranceHistoryLocal_schedule h44 hκ hκ4 c₀ hc₀ hh s hE hreg hu₀
  have hG := ae_isGoodSched h44 hκ hκ4 c₀ hc₀ hh s hE hreg
  refine ⟨α, hαc, hα0, hαm, hαtr, fun n hn => ?_⟩
  refine isHistoryAvoidanceLocal_range_of_path_schedule h44 hκ hκ4 c₀ hc₀ hh s hE hreg u₀ hαc hα0 hαm
    (r := recPath s n) (measurable_recPath s n) (fun t => ?_) (ψ := pastOfPath s n) (measurable_pastOfPath s n) ?_
    (hloc (n + 1) hn)
  · filter_upwards [hG, hαtr] with ω hg hα
    exact hg.frozenPath_eq_recPath hreg hα hn t
  · filter_upwards [hG, hαtr] with ω hg hα
    exact hg.pastMap_eq_pastOfPath hα hn

end Main

end InteractingSLE.Sec5.CrossCond.StagedGlue
